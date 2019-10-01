module Main

import Data.Vect

data VectUnknown : Type -> Type where
  MkVect : (len : Nat) -> Vect len a -> VectUnknown a

readVect : IO (VectUnknown String)
readVect = do x <- getLine
              if (x == "")
                 then pure (MkVect _ [])
                 else do (MkVect _ xs) <- readVect
                         pure (MkVect _ (x :: xs))

readVect' : IO (len : Nat ** Vect len String)
readVect' = do x <- getLine
               if (x == "")
                  then pure (_ ** [])
                  else do (_ ** xs) <- readVect'
                          pure (_ ** (x :: xs))


threes : Vect 3 a -> a
threes (x :: xs) = x

main : IO ()
main = do (n ** xs) <- readVect'
          answer <- pure (
                 case n of
                      S (S (S Z)) => threes xs
                      _ => "not three!"
          ) 
          putStrLn answer
