import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Free
import Control.Monad.Trans.Writer
import Control.Pipe

-- Merge two input streams into a Producer stream
-- I could combine the second Consumer layer with the Producer layer into a
--   single Pipe, but I want to separate out the two application steps for this
--   example
merge :: (Monad m) => Consumer Int (Consumer Int (Producer Int m)) r
merge = do
    x <- await       -- Read from the first consumer
    y <- lift await  -- Read from the second consumer
    merge' x y

merge'
 :: (Monad m)
 => Int
 -> Int
 -> Consumer Int (Consumer Int (Producer Int m)) r
merge' x y =
    if (x <= y)
    then do
        lift $ lift $ yield x
        x' <- await
        merge' x' y
    else do
        lift $ lift $ yield y
        y' <- lift await
        merge' x y'

stream1, stream2 :: (Monad m) => Producer Int m ()
stream1 = mapM_ yield [1, 3, 5, 7]
stream2 = mapM_ yield [2, 4, 6, 8]

-- Now it is a function of a single stream after being applied to one producer
firstApplication :: (Monad m) => Consumer Int (Producer Int m) ()
firstApplication = runPipe $ merge <+< stream1

-- Now it is fully applied, reducing to a Producer
-- Note that the base monad is polymorphic so it is still 100% pure
secondApplication :: (Monad m) => Producer Int m ()
secondApplication = runPipe $ firstApplication <+< stream2

-- Pure fold over input
collect :: Consumer Int (Writer [Int]) r
collect = forever $ await >>= lift . tell . return

main = print $ execWriter $ runPipe $ collect <+< secondApplication
{- Prints: [1,2,3,4,5,6,7]

   This does not print 8 because merge does not intercept upstream termination
     when it tries to read another value from stream1 to replace the 7

   There are three solutions I know of:
     a) Use Maybe Int with Nothing to signal termination
     b) Use an indexed monad
     c) Don't use composition at all

   By (c), I mean writing a direct function of the type:

   merge :: Producer Int m r -> Producer Int m r -> Producer Int m r

   ... that manually deconstructs the two arguments and reassembles them, much
   as you would with an ordinary list merge.  I've written it up below:
-}

pop :: (Monad m) => Producer b m r -> m (Maybe (b, Producer b m r))
pop p = do
    x <- runFreeT p
    case x of
        Pure          _   -> return   Nothing
        Free (Await   f ) -> pop $ f ()
        Free (Yield b p') -> return $ Just (b, p')

merge2 :: (Monad m, Ord b) => Producer b m r -> Producer b m r -> Producer b m r
merge2 p1 p2 = do
    x1 <- lift $ pop p1
    case x1 of
        Nothing        -> p2
        Just (b1, p1') -> do
            x2 <- lift $ pop p2
            case x2 of
                Nothing        -> yield b1 >> p1'
                Just (b2, p2') -> merge2' b1 b2 p1' p2'

merge2'
 :: (Monad m, Ord b)
 => b -> b -> Producer b m r -> Producer b m r -> Producer b m r
merge2' b1 b2 p1 p2 =
    if (b1 <= b2)
    then do
        yield b1
        x1 <- lift $ pop p1
        case x1 of
            Nothing -> yield b2 >> p2
            Just (b1', p1') -> merge2' b1' b2 p1' p2
    else do
        yield b2
        x2 <- lift $ pop p2
        case x2 of
            Nothing -> yield b1 >> p1
            Just (b2', p2') -> merge2' b1 b2' p1 p2'

main2 = print $ execWriter $ runPipe $ collect <+< merge2 stream1 stream2
{- Prints: [1,2,3,4,5,6,7,8]

   Personally, I think this last solution is probably best for what you want,
   but I still wanted to demonstrate the general principle for combining
   multiple pipeline layers. -}