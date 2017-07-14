Record Signature (I O : Type) : Type := {
    Operations : O → Type;
    Arities    : forall o : O, Operations o → Type;
    Sorts      : forall (o : O) (op : Operations o), Arities o op → I
}.
