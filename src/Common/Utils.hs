module Common.Utils where

import Data.Bifunctor            ( first )

-- index of element in a list
indexOf :: Eq a => [a] -> a -> Maybe Int
indexOf [] _ = Nothing
indexOf (x:xs) y = if x == y then Just 0 else (1+) <$> indexOf xs y

-- returns both index and value
lookupIndex :: Eq a => [(a, b)] -> a -> Maybe (Int, b)
lookupIndex [] _ = Nothing
lookupIndex ((x, z):xs) y = if x == y then Just (0, z) else first (1+) <$> lookupIndex xs y