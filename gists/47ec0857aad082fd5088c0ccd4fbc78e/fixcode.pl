#!/usr/bin/env perl

while (<>) {
    s/import qualified Prelude/import qualified Prelude\nimport qualified HString\nimport qualified Data.Char\nimport qualified Data.List\nimport qualified Data.Ratio\nimport qualified GHC.Real\nimport qualified Data.Function\nimport qualified Data.Maybe\nimport Debug.Trace/;
    s/unsafeCoerce :: a -> b/--unsafeCoerce :: a -> b/;
    s/\bfun /\\/;
    s/\brec\b/rec_/;
    s/\(=\)/(Prelude.==)/;
    s/\(<=\)/(Prelude.<=)/;
    s/\(<\)/(Prelude.<)/;
    s/\(>\)/(Prelude.>)/;
    s/\(\+\)/(Prelude.+)/;
    s/\(==\)/(Prelude.==)/;
    s/Pervasives\.min/(Prelude.min)/;
    s/Pervasives\.max/(Prelude.max)/;
    s/if n>m then None else Some \(n<m\)/if n Prelude.> m then Prelude.Nothing else Prelude.Just \(n Prelude.< m\)/;
    s/b = \(Prelude\.<=\) \(\(Prelude.succ\)/b = ((Prelude.<=) :: Prelude.Double -> Prelude.Double -> Prelude.Bool) ((Prelude.succ)/;
    s/getcMethDef n' methSigs methDefs \(unsafeCoerce idx\)/getcMethDef n' methSigs (unsafeCoerce methDefs) (unsafeCoerce idx)/;
    s/Prelude.True -> seval_production_coords pt0 seval_productions0/Prelude.True -> unsafeCoerce seval_production_coords pt0 seval_productions0/;
    s/\(ilist2_tl \(HString\.nsucc/(unsafeCoerce (ilist2_tl (HString.nsucc/;
    s/          components\)\)}/          components)))}/;
    print;
}
