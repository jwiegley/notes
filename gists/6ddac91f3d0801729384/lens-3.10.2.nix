  preConfigure = ''
    sed -i -e 's/contravariant.*1/contravariant >= 0.3 \&\& < 2/' lens.cabal
    sed -i '/Instances/d' lens.cabal
    sed -i -e 's/import Control\.Lens\.Internal\.Instances \(\)/import Data.Semigroup.Foldable ()\nimport Data.Semigroup.Traversable/' \
      src/Control/Lens/Internal/Indexed.hs
    sed -i '/Instances/d' src/Control/Lens/Internal.hs
    rm -f src/Control/Lens/Internal/Instances.hs
  '';
