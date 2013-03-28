select :: [a] -> [[a]]
select [] = []
select (x : xs) = (x, xs) : map (fmap (x :)) (select xs)