    Just (k :: ((Int, Int), Int) -> Int) <-
        case ccc @(NonDet ((->) :**: Gather)) program of
            NonDet (g :: p -> ((->) :**: Gather) ((Int, Int), Int) Int) ->
                fmap (fmap ((\(p :**: _) -> p) . g))
                    $ runZ3 $ ccc @Z3Cat $ \(x :: p) ->
                        let _ :**: Gather s = g x in s < 100
