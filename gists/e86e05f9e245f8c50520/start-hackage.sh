curl -s -o - http://hackage.haskell.org/packages/index.tar.gz   \
    | gzip -dc | pv -s $size                                    \
    > ~/.cabal/packages/hackage.haskell.org/00-index.tar
