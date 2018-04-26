Definition foo (n : nat) : nat :=
  n.

Definition bar (n : nat) : nat := foo n.

Require Extraction.

Inductive Instrument : Type :=
  | I_foo (n : nat) : Instrument.

Definition wrap (i : Instrument) {A : Type} (x : A) := x.
Extract Constant wrap => "\x d -> unsafePerformIO (x <$ modifyIORef events (d:))".

Definition foo' := Eval unfold foo in foo.
Definition foo_ n := foo' (wrap (I_foo n) n).
Extract Constant foo => "foo_".

Extraction Language Haskell.

Set Extraction KeepSingleton.
Set Extraction AutoInline.
Set Extraction Optimize.
Set Extraction AccessOpaque.

Extraction "Wrap.hs"
  bar wrap foo foo' foo_ Instrument I_foo.
