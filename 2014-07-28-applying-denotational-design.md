---
title: Applying denotational design ideas
description: desc here
tags: haskell
date: [2014-07-28 Mon 20:52]
category: Haskell
---

While I was at LambdaJam last week, I participated in a workshop by Conal
Elliot on
[Denotational Design](https://github.com/conal/talk-2014-lambdajam-denotational-design):
a way of stepping back from implementation concerns to define denotations, or
mappings from concepts to meanings, that express the real intent of a
program's design.  Conal gave a similar presentation at BayHac a few months
ago, for which the video is [here](https://www.youtube.com/watch?v=zzCrZEil9iI).

<!--more-->

I decided to try out Conal's ideas by applying them to a problem I had solved
a few different ways while working at FP Complete: how to manage execution of
many concurrent tasks, where some of the tasks may depend on others in
flexible ways.

## The design phase

I was never entirely happy with the solutions I came up with before, so I
thought maybe denotational design could help guide me toward a purer solution;
and I must say, within only a few hours of pondering it did just that.

First of all, my error in the past was that I thought in terms of threads and
control structures, STM and async and lambda abstractions, etc.  What Conal
prompts us to do is to think in terms of the most basic abstractions possible.
What is a task?  What is concurrency?  What do the words I'm using really
mean?

This brought the problem down to just a few, core types (where by types I mean
mathematical types, not anything you would write in code just yet): Tasks,
Collections of tasks, and Dependencies between tasks.  These convey the
meaning of the problem I'm trying to solve.

If that's all I'm working with, then the whole of the problem is really a
partially ordered set.  This leads to a fairly complete statement of the
design I want to work with:

"A set of tasks is a partially ordered set, where for any two related tasks x
<= y, x must execute before y; and for any two unrelated tasks w and v, w may
execute concurrently with v."  By iterating over this set and removing each
task as it completes, we will eventually execute each task in the correct
order.

Notice how this expression of the problem, while basic, encompasses every
possible dependency structure.  Perhaps many tasks are blocked on one task, or
one task awaits many tasks, or both.  Acyclic relationships are made
impossible by the asymmetric nature of partial orders: the only way for x and
y to be mutually dependent is for them to be the self-same task.

Moreover, the theory behind partial orders gives me ways to reason about task
collections.  There is clearly a "concurrent subset": the set of tasks ready
to execute in parallel.  This is formally the downward closed subset of the
collection.  Each round of execution then consists of finding this subset, and
forking off each one.  Repeat until done.

## The mapping phase

After the design phase is completed, I have my meanings.  The next step is to
map those meanings onto representations.  I can't actually going to work with
partially ordered sets, since that is a mathematical abstraction.  Rather, I
will use data structure and/or functions capable of expressing partially
ordered sets.  For example, I know that I need a function to add tasks to a
set, one to find the downward closed subset, one to remove elements from the
set, etc.

I could naively use Haskell's Set data structure, but finding the downward
closed subset requires iterating through the set in O(n^2) complexity,
computing the relationships between the members.  A more efficient
representation is to use a directed acyclic graph, where an edge from task A
to task B means that A must complete before B can begin.  Now find the subset
I want only requires O(n) complexity: I just filter out every node which is
the target of an edge.

This can even happen lazily, since I only need to know about N tasks at any
given time, in order to bound to number of concurrent jobs.  I associate
"slots" with the task collection (just a number), and only execute new tasks
when a slot becomes free.

Lastly, I need to keep track of the result values for each task, which is done
using a separate mapping from integers to `Async` actions.  This way we record
not only the result value, but any exception that may have terminated the
thread.  If the user never cares to see this information, they can add an
action at the end of their job to fork off another thread that waits on this
information, clearing the result from the map.  Alternatively I could add a
function to submit a task that will throws its final result, in case we only
care about the side-effects.

## The taskpool package

There you have it, a way to concurrently execute sets of task with arbitrarily
dependency relationships, using at most N execution slots at a time.  The code
is simple, efficient, and easy to reason about.  The first version is on
Hackage now:

    http://hackage.haskell.org/package/taskpool-0.0.1/docs/Data-TaskPool.html
    
Many thanks to Conal for his great presentation, and for changing the way I
think about program design.  Taskpool only took one day to write, and yet
never before had the idea of a graph representation of a partially ordered set
occurred to me, since I was too focused on typical implementation strategies
to see it.
