data Generator s = Generator
newtype Generatee s = Generatee Integer

newGenerator :: Generator s
newGenerator = Generator

generate :: Generator s -> (Generator s, Generatee s)
generate = undefined

reduce :: Generatee s -> Integer
reduce (Generatee num) = num

runGenerator :: (forall s. ((Generator s -> (Generator s -> a) -> a) -> a)) -> a
runGenerator go = go $ flip ($)

sourceGenerator :: Monad m => (forall s. Generator s) -> Source m Integer
sourceGenerator generator = source $ go generator
  where
    go start z yield = loop start z
      where
        loop gen r =
            let (gen', g) = generate gen
            in yield r (reduce g) >>= loop gen'

test_ :: IO ()
test_ = do
    xs <- sinkList $ takeC 10 $ sourceGenerator newGenerator
    print xs
