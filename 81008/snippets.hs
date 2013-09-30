foo = filter (odd . fst) . map fn . tails
    where fn (x:y:xs) = (x,y)
          fn _ = (0, 0)
