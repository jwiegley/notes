(****************************************************************************)
(* The Simple Parser Vignette (SPV)                                         *)
(****************************************************************************)

Require Import
  Vignettes.SPV_fidl
  Fiat.ADTRefinement
  Fiat.ADTRefinement.BuildADTRefinements.

Require Import Fiat.Parsers.Refinement.Tactics.

Generalizable All Variables.

Import ListNotations.
Open Scope list_scope.

Section SPVParser.

Variable params : TunableParameters.
Variable mon : MonitorPredicates params.

Lemma ComputationalSplitter' :
  FullySharpened (string_spec (spvGrammar params) String.string_stringlike).
Proof.
  Require Import Fiat.Parsers.Refinement.DisjointRules.

  splitter_start.
  {
    rewrite_disjoint_search_for.
    splitter_finish.
  }
  splitter_finish.
Defined.

Lemma ComputationalSplitter :
  FullySharpened (string_spec (spvGrammar params) String.string_stringlike).
Proof.
  Time make_simplified_splitter ComputationalSplitter'.
Defined.

Definition parser :
  ParserInterface.Parser (spvGrammar params) String.string_stringlike.
Proof.
  let b := make_Parser ComputationalSplitter in
  exact b.
Defined.

Definition parser_informative_opaque (str : string)
  : option (parse_of_item (spvGrammar params) str
                          (NonTerminal (Start_symbol (spvGrammar params)))).
Proof.
  Time make_parser_informative_opaque ComputationalSplitter.
Defined.

Definition parser_informative (str : Coq.Strings.String.string)
  : option (@simple_parse_of_item Ascii.ascii).
Proof.
  Time make_parser_informative ComputationalSplitter.
Defined.

Section eval.
  Require Import Fiat.Parsers.Grammars.EvalGrammarTactics.

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
               | SimpleParseNonTerminal _ _ => _
             end.
      destruct (string_dec nt "expr").
        exact (list (@Tuple (spvRow params))).
      destruct (string_dec nt "coords").
        exact (@Tuple (spvRow params)).
      destruct (string_dec nt "nat").
        exact N.
      destruct (string_dec nt "float").
        exact R.
      destruct (string_dec nt "dotted").
        exact R.
      destruct (string_dec nt "neg").
        exact R.
      destruct (string_dec nt "WS+").
        exact unit.
      exact unit.
    }
  Defined.

  Fixpoint seval_productions (pt : @simple_parse_of Ascii.ascii) :
      sevalT_productions pt
    with seval_production (pt : @simple_parse_of_production Ascii.ascii) :
      sevalT_production pt
    with seval_item (pt : @simple_parse_of_item Ascii.ascii) : sevalT_item pt.
  Proof.
    { destruct pt; simpl; eauto with nocore. }
    { destruct pt; simpl; eauto using tt, pair with nocore. }
    { destruct pt as [ch|nt pt]; simpl.
        exact tt.
      specialize (seval_productions pt).
      revert seval_productions.
      destruct (string_dec nt "expr") eqn:Heqe1;
      [ | destruct (string_dec nt "coords") eqn:Heqe2;
      [ | destruct (string_dec nt "nat") eqn:Heqe3;
      [ | destruct (string_dec nt "float") eqn:Heqe4;
      [ | destruct (string_dec nt "dotted") eqn:Heqe5;
      [ | destruct (string_dec nt "neg") eqn:Heqe6;
      [ | destruct (string_dec nt "WS+") eqn:Heqe7;
      [ | exact (const tt) ] ] ] ] ] ] ].

      (* ("expr" ::== "coords" || "coords" \n "expr") *)
      refine match pt return sevalT_productions pt -> list Tuple with
             | SimpleParseHead (SimpleParseNonTerminal "coords" _::[]) =>
               fun v => [fst v]
             | SimpleParseTail
                 (SimpleParseHead
                    (SimpleParseNonTerminal "coords" _ ::
                     SimpleParseTerminal _ ::
                     SimpleParseNonTerminal "expr" _ :: [])) =>
               fun v => fst v :: fst (snd (snd v))
             | _ => const nil
             end.

      (* ("coords" ::== "nat" "WS+" "float" "WS+" "float") *)
      refine match pt return sevalT_productions pt -> Tuple with
             | SimpleParseHead
                 (SimpleParseNonTerminal "nat" _ ::
                  SimpleParseNonTerminal _ _ ::
                  SimpleParseNonTerminal "float" _ ::
                  SimpleParseNonTerminal _ _ ::
                  SimpleParseNonTerminal "float" _ :: []) =>
               fun v =>
                 < sPOINT_SEQ  :: 0%nat
                 , sPOINT_TIME :: fst v
                 , sPOINT_LAT  :: fst (snd (snd v))
                 , sPOINT_LON  :: fst (snd (snd (snd (snd v)))) >
             | _ =>
               fun _ =>
                 < sPOINT_SEQ  :: 0%nat
                 , sPOINT_TIME :: 0%N
                 , sPOINT_LAT  :: 0%R
                 , sPOINT_LON  :: 0%R >
             end.

      (* ("nat" ::== [0-9] || [0-9] "nat") *)
      refine match pt return sevalT_productions pt -> N with
             | SimpleParseHead (SimpleParseTerminal ch::[]) =>
               fun _ => (N_of_ascii ch - 48)%N (* opt.nat_of_ascii "0" is 48 *)
             | SimpleParseTail
                 (SimpleParseHead
                    (SimpleParseTerminal ch ::
                     SimpleParseNonTerminal "nat" _ :: []))
               => fun v => ((N_of_ascii ch - 48) * 10 + fst (snd v))%N
             | _ => const 0%N
             end.

      (* ("float" ::== "dotted" || "neg") *)
      refine match pt return sevalT_productions pt -> R with
             | SimpleParseHead (SimpleParseNonTerminal "dotted" _::[]) => fst
             | SimpleParseTail
                 (SimpleParseHead
                    (SimpleParseNonTerminal "neg" _ :: [])) => fst
             | _ => const 0%R
             end.

      (* ("dotted" ::== "nat" "." "nat") *)
      Require Import Vignettes.Q2R.
      refine match pt return sevalT_productions pt -> R with
             | SimpleParseTail
                 (SimpleParseHead
                    (SimpleParseNonTerminal "nat" _ ::
                     SimpleParseTerminal _ ::
                     SimpleParseNonTerminal "nat" _ :: []))
               => fun v => NN2R (fst v) (fst (snd (snd v)))
             | _ => const 0%R
             end.

      (* ("neg" ::== "-" "dotted") *)
      refine match pt return sevalT_productions pt -> R with
             | SimpleParseTail
                 (SimpleParseHead
                    (SimpleParseTerminal _ ::
                     SimpleParseNonTerminal "dotted" _ :: []))
               => fun v => (0 - fst (snd v))%R
             | _ => const 0%R
             end.

      (* ("WS+" ::== WS || WS "WS+") *)
      exact (const tt).
    }
  Defined.
End eval.

Definition parser_eval (str : string) : option (list (@Tuple (spvRow params))).
Proof.
  refine match parser_informative str with
         | Some (SimpleParseNonTerminal nt pt)
           => let n := seval_item (SimpleParseNonTerminal "expr" pt) in
              Some n
         | Some (SimpleParseTerminal _) => None
         | None => None
         end.
Defined.

End SPVParser.
