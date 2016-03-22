  Fixpoint sevalT_productions (pt : @simple_parse_of Ascii.ascii) : Type
  with sevalT_production (pt : @simple_parse_of_production Ascii.ascii) : Type
  with sevalT_item (pt : @simple_parse_of_item Ascii.ascii) : Type.
  Proof.
    { refine match pt with
               | SimpleParseHead pt' => sevalT_production pt'
               | SimpleParseTail pt' => sevalT_productions pt'
             end. }
    { refine match pt return Type with
               | SimpleParseProductionNil => unit
               | SimpleParseProductionCons p ps =>
                   (sevalT_item p * sevalT_production ps)%type
             end. }
    { refine match pt return Type with
               | SimpleParseTerminal ch => unit
               | SimpleParseNonTerminal n _ =>
                   match n with
                   | "expr"   => list (@Tuple (spvRow params))
                   | "coords" => @Tuple (spvRow params)
                   | "nat"    => N
                   | "float"  => R
                   | "dotted" => R
                   | "neg"    => R
                   | "WS+"    => unit
                   | _        => _
                   end
             end. }
  Defined.
