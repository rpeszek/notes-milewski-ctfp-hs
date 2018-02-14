|Markdown version of this file: https://github.com/rpeszek/notes-milewski-ctfp-hs/wiki/N_P3Ch07a_GameOfLife

Notes related to CTFP Part 3 Chapter 7. Comonads. Game of Life Example
======================================================================

Implementation of Conway's Game of life 
[wikipedia](https://en.wikipedia.org/wiki/Conway%27s_Game_of_Life)
using store comonad.
This solves the challenge problem from 
[CTFP](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/)
[P3 Ch7 Comonads](https://bartoszmilewski.com/2017/01/02/comonads/).
  

> module CTNotes.P3Ch07a_GameOfLife where
> import Control.Comonad
> import Control.Lens ((^?), element)  -- for auxiliary util code
> import Data.Maybe (fromMaybe)
> import Data.Bool (bool)
> import Utils.Stream (Stream, streamIterate)
> import qualified Utils.Pretty as Pretty 

Store
-----
From the book

> data Store s a = Store (s -> a) s
> instance Functor (Store s) where
>   fmap f (Store fs s) = Store (f . fs) s 
> instance Comonad (Store s) where
>   extract (Store f s) = f s
>   duplicate (Store f s) = Store (Store f) s
  
Helpers
-------

> neighbors :: [(Int, Int)]
> neighbors =  filter (/= (0,0)) ((,) <$> [-1..1] <*> [-1..1]) 
> 
> vAdd :: (Int, Int) -> (Int, Int) -> (Int, Int)
> vAdd (x1,y1) (x2,y2) = (x1 + x2, y1 + y2)

Standard Stream implementation and helper `streamIterate` function is loaded from Utils.Stream. 

Implementation
--------------

> type Conway = Store (Int, Int) Bool
>
> conwayArrow :: Conway -> Bool
> conwayArrow (Store fs xy) = 
>            let neighList = map (vAdd xy) neighbors 
>                liveNeighbors = length $ filter id $ map fs neighList
>                cell = fs xy
>            in if liveNeighbors > 3 || liveNeighbors < 2
>               then False
>               else if liveNeighbors == 3
>                  then True
>                  else cell   
>
> conwayStep :: Conway -> Conway 
> conwayStep  = extend conwayArrow
>
> conwayStream :: Conway -> Stream Conway
> conwayStream initPopulation = streamIterate conwayStep initPopulation

Demo
----

> storeToList :: Int -> Store (Int, Int) a -> [[a]]
> storeToList i (Store fs s) = 
>      let row iy = map (\ix -> fs ((ix, iy) `vAdd` s)) [-i..i]
>      in  row <$> [-i..i]   
> 
> -- for 3x3 use offsets 1, 1 to nicely center
> listToStore :: a -> Int -> Int-> [[a]] ->  Store (Int,Int) a
> listToStore defV xoffset yoffset list = 
>      let safeElemAt :: a -> Int -> [a] -> a
>          safeElemAt defV i list = fromMaybe defV $ list ^? element i
>          fs (x, y) = safeElemAt defV x $ safeElemAt [] y list
>      in Store fs (xoffset,yoffset)     
>
> testConway:: Int -> Int -> Int -> [[Int]] -> IO ()
> testConway outputSize offset noSteps population = 
>      let toBool :: [[Int]] -> [[Bool]] 
>          toBool = (map . map) ((==) 1) 
>          toInt :: [[Bool]] -> [[Int]]
>          toInt = (map . map) (bool 0 1) 
>          conwayIntStream :: Stream [[Int]]
>          conwayIntStream =  fmap (toInt . storeToList outputSize) $ conwayStream $ listToStore False offset offset (toBool population)
>      in Pretty.streamOfNestedListsPrint noSteps conwayIntStream 


ghci outputs:
```
-- blinker (period 2)
ghci> testConway 2 1 2 [[1,0,0],[1,0,0],[1,0,0]]
[0,0,0,0,0]
[0,1,0,0,0]
[0,1,0,0,0]
[0,1,0,0,0]
[0,0,0,0,0]

[0,0,0,0,0]
[0,0,0,0,0]
[1,1,1,0,0]
[0,0,0,0,0]
[0,0,0,0,0]

ghci> testConway 2 1 3 [[0,1,0],[1,1,1],[0,1,0]]
[0,0,0,0,0]
[0,0,1,0,0]
[0,1,1,1,0]
[0,0,1,0,0]
[0,0,0,0,0]

[0,0,0,0,0]
[0,1,1,1,0]
[0,1,0,1,0]
[0,1,1,1,0]
[0,0,0,0,0]

[0,0,1,0,0]
[0,1,0,1,0]
[1,0,0,0,1]
[0,1,0,1,0]
[0,0,1,0,0]

-- Tub (stable)
ghci> testConway 2 1 1 [[0,1,0],[1,0,1],[0,1,0]]
[0,0,0,0,0]
[0,0,1,0,0]
[0,1,0,1,0]
[0,0,1,0,0]
[0,0,0,0,0]
```
