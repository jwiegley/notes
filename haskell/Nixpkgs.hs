module Nixpkgs where

import Control.Lens
import Data.Map

type Pkgs = Map String String

-- An extension function always receives two arguments: self and super.
--
-- 'super' is the package set state *up to that override function*. Thus, you
-- can always refer to entries in 'super' without fear of infinite recursion.
--
-- 'self' is the completed package set after all overrides have been
-- performed. This works due to laziness, and requires that every tree of
-- attributes forced after overriding is an acyclic graph.
--
-- Thus, you will often see:
--
-- { foo = super.foo.override { ... }; }
--
-- But the following results in an infinite recursion:
--
-- { foo = self.foo.override { ... }; }
--
-- Yet this does not:
--
-- { foo = super.foo.override { ... };
--   bar = self.foo;  # use the overriden foo on the previous line
-- }

type ExtFun = Pkgs {- self -} -> Pkgs {- super -} -> Pkgs

override1 :: Pkgs -> Pkgs -> Pkgs
override1 self super =
  super
    & at "alpha" ?~ "beta"
    & at "foo"
      ?~ super ^?! ix "foo" ++ self ^?! ix "alpha"

override2 :: Pkgs -> Pkgs -> Pkgs
override2 _self super = super

composeExtensions :: ExtFun -> ExtFun -> ExtFun
composeExtensions f g = \self -> f self . g self

runExtensions :: ExtFun -> Pkgs -> Pkgs
runExtensions f pkgs = let self = f self pkgs in self

main :: IO ()
main =
  -- Prints: fromList [("alpha","beta"),("foo","is_foobeta")]
  print
    ( runExtensions
        (composeExtensions override1 override2)
        (empty & at "foo" ?~ "is_foo")
    )
