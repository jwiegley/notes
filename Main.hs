        foldM (\(y, ys) x -> do
                  (x',xs') <- gatherSizes opts (curDepth + 1) (collapse x)
                  let x''  = y <> x'
                      xs'' = if curDepth < depth opts
                             then ys <> DL.singleton x' <> xs'
                             else DL.empty
                  return $! x'' `seq` xs'' `seq` (x'', xs''))
              (newEntry path True, DL.empty) =<< listDirectory path
