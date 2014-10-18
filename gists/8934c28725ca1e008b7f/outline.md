Code repository: https://github.com/jwiegley/linearscan

Original article: https://www.usenix.org/legacy/events/vee05/full_papers/p132-wimmer.pdf

* The Problem

The desire was to create a Haskell library implementing a linear scan register
allocator.  A paper documenting a suitable algorithm was found, but there was
interest in building it in a verified context, as a real-world test of that
methodology, compared to similar engineering efforts in Haskell.

The algorithm is fairly clearly documented, with pseudo-code and examples.
The goal was to take this document as a formal specification, and then build a
library in Coq -- with extracting to Haskell -- whose types and supporting
lemmas would be sufficiently expressive so that *only correct implementations
would typecheck*.  After that, the only parameter of choice should be choosing
which efficiency dimensions to optimize for.

* Architecture

Rendering the paper's algorithm into code meant first choosing appropriate
types, and identifying all assumptions.  The following is a summary of those
identified [this part may be in the paper, but not in the presentation].

** Use Positions

When code is linearized for the purposes of register allocation, each position
where a variable is used is termed a "use position".  There is also a boolean
flag to indicate whether a register is required at a use position or not.

  Requirements:
  - All use positions must be even, so that ranges do not extend to the next
    use position.

** Ranges

A set of use positions constitutes a range, from the beginning to 1+ the last.
However, a range may also be extended so that it's beginning and ending may
fall outside of its set of use positions.  This is done to provide coverage of
loop bodies, to avoid reloading a register each time the loop is executed.

  Requirements
  - The set of use positions is ordered with respect to location.
  - The set of use positions is unique with respect to location (no recurring
    positions).
  - The beginning of a range is also <= its first use position.
  - The end of a range is also > its last use position.

** Intervals

A set of ordered ranges constitutes an interval.  In the majority of cases,
intervals are equivalent to ranges, since only a single range is used.
However, adding the concept of intervals allows for "lifetime holes" between
ranges that are otherwise allocated to the same register.

  Requirements
  - The set of ranges is ordered with respect to the first use position of
    each range.
  - The set of ranges is non-overlapping.
  - The beginning of the interval corresponds to the beginning of its first
    range.
  - The end of the interval corresponds to the end of its last range.

** The Scan State

During the course of the algorithm, a position counter is iterated from the
first code position to the last.  Six separate details are then managed within
a group of indexed vectors:

  1. A list of yet to be allocated intervals (unhandled intervals)
  2. A list of active intervals (those covering the current position, and
     presently allocated)
  3. A list of inactive intervals (those which have a lifetime hole covering
     the current position)
  4. A list of handled intervals
  5. A mapping from registers to active/inactive/handled intervals
  6. A mapping from intervals (those not unhandled) to registers

  Requirements
  - The list of unhandled intervals is ordered by start position
  - The first 4 lists, taken as a set, must contain no recurring intervals,
    and have no overlapping intervals
  - All register indices must be < maximum register

* Design

This was the implementor's first experience with Coq at this scale, and so
many mistakes were made that led to refactoring and refinements.  This meant
the design went through several iterations, which led to many realizations
about the building of such systems in Coq.

** First design: Purely computational

In the first iteration, I approached the task much as a Haskell programmer
might: data types carried computationally relevant information, functions were
implemented in a straightforward fashion, and reasoning was extracted to
lemmas applied to these types and functions.  There were almost no dependent
types involved, and very few inductive types.  Most of the types used were
records.

In the beginning this seemed a relatively simple and painless approach, until
I encountered the necessity of proving termination for the main Fixpoint
definition: the entry-point into the linear scan algorithm.

At first this seemed like a straightforward thing to prove, but quickly became
intractable.  In effect, proving a purely computational algorithm of this
complexity meant using tactics to explore every possibility at each step of
the algorithm: in effect, re-implementing the same algorithm in reverse, only
now in the tactics language.

This led very quickly to the realization that dependent types and inductive
types would be necessary to capture evidence determined via computation at the
lower levels of the algorithm, so that it could percolate back up to the
higher levels where it was needed.

** Second design: Mostly dependent inductive

The switch to dependent records allowed for evidence to be produced one, and
then carried around, but after a little while this became unfeasible as well.
The issue was that types very often did not unify, require auxiliary lemmas
who sole purpose was to "transport" evidence from one context to another.

** Third design: Split structure: non-dependent and dependent

The third iteration on the design divided the information from each of the
core data types mentioned above into two categories:

  - Non-dependent records carrying computationally-relevant content only, in
    Set.

  - Dependent inductive types carrying propositionally-relevant content only,
    in Prop.

This division provided me with "proof-embedded data", which allowed for simple
transformation of the underlying data when necessary, and inductive on
propositional evidence when required.  The division of labor clarified not
only the proofs, but made many constructions far simpler to manage.  This is
the final design that was settled upon, with one additional twist.

** Third design extension: Proof morphisms

Whenever proof-embedded data was produced by a function, very often that same
data would get transformed by another function soon after.  Such
transformations modify the underlying data and adjust the type of the evidence
accordingly -- sometimes even strengthening or weakening the associated
propositions.

Some transformations became so common that a recurring structure was observed
*among* functions.  These morphisms were codified using dependent records, to
maintain a trail of connecting evidence: proving all the ways that values of
certain types could be modified by a composition of functions.  The act of
composition itself recorded the manner in which the associated properties had
been strengthened or weakened.

The proper abstraction for such "contextual composition" is, of course,
composition in a Kleisli category.  Indexed monads were chosen as a way of
directly expressing the input and output conditions in the types of the
functions.  These conditions depended on a relation with the "original" value,
from the beginning of the composition, such that certain facts could be known
about the final value in relation to the initial one.

By this means, the algorithm procedure could be rewritten in a monadic style
without requiring explicit management of intermediary evidence, while the
termination proof of the main algorithm became a one-liner:

  Proof. intros; clear; by case: ssinfo' => ?; case=> /= _ /ltP. Qed.

* Code extraction

A primary goal of this endeavor, from the very beginning, was extraction to
Haskell.  In fact, the algorithm was needed for a compiler, and so would be
written for Haskell one way or another.  The question is whether Coq and
formal methods would be up to the task of building it a better way.

About midway through the development, focus was turned toward producing
reasonable Haskell code through Coq's built-in extraction facilities.  These
allow for:

  - Extraction of functions and types (those not in Prop), and all their
    related definitions.

  - Association of types and constructors with native Haskell types, for
    efficiency (although "Int" is a major exception [note here about Adam's
    "accel" project])

  - Renaming certain library functions to use their Haskell counterparts
    (which of course requires that they be trusted to be both total and
    correct).

There is unfortunately no published meta-theory for the extraction process in
Coq, and indeed some very glaring bugs were encountered during this project
(including one where type variables were inexplicable swapped in a constructor
whenever auto-inlining was used).

Even still, the ability to write code in Coq and have it so easily converted
to naive Haskell was incredibly useful, and an area that I hope sees further
development effort.

* Lessons learned

One of the main lessons learned is that Coq is a fantastic environment in
which to reason about code and algorithms!  It required me to fully grasp
every single nook and cranny of this algorithm, including all of its unwritten
assumptions -- details which would be all too easy to neglect in a freer
language.

Another lesson is that using Coq well requires both education and experience.
This effort too far longer than expected, and much, much longer than the
equivalent Haskell would have been to write.  That said, many of the worst
design mistakes that I made were solely due to inexperience with using Coq in
this way, and are not likely to be made again on future projects.

The Proof General environment in Emacs, the prooftree visualization tool, and
the ssreflect library, were all invaluable in providing a better experience at
using Coq.  I truly felt I was able to "dialog with my types", leading to a
richer understanding and better decisions.
