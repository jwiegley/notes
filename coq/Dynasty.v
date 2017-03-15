Record MyRecord : Type := {
  field1 : nat;
  field2 : nat
}.

Record CorrectRecord (r : MyRecord) : Prop := {
  _ : field1 r + field2 r > 0
}.

Inductive ConstructedRecord : MyRecord -> Prop :=
  | Initialize : ConstructedRecord {| field1 := 0; field2 := 0 |}
  | AddToField1 : forall (r : MyRecord) (n : nat), n >= 0 ->
      ConstructedRecord {| field1 := field1 r + n; field2 := field2 r |}
  | AddToField2 : forall (r : MyRecord) (n : nat), n >= 0 ->
      ConstructedRecord {| field1 := field1 r; field2 := field2 r + n |}.
