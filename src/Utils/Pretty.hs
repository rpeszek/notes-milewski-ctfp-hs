module Utils.Pretty where
import Data.Monoid((<>))
import Utils.Stream
import Control.Monad(mapM_)

nestedListPrint :: Show a => [[a]] -> IO()
nestedListPrint list = putStrLn $ foldr (<>) "" $ map (\l -> show l <> "\n") list

streamOfNestedListsPrint :: Show a => Int -> Stream [[a]] -> IO()
streamOfNestedListsPrint count stream = mapM_ (nestedListPrint) $ streamToList count stream 
