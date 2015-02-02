Fixpoint HStream_run {a : Type} (h : HStream a a) (n : nat) {struct n} : option a :=
  match n with
  | O => None
  | S n' => match h with
    | f :<<: fs => match HStream_run fs n' with
      | None => None
      | Some x => Some (f x)
      end
    end
  end.
