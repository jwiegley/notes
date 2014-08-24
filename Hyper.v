CoFixpoint HStream_run {a : Type} (h : HStream a a) : a :=
  match h with
  | f :<<: fs => f (HStream_run fs)
  end.
