module Main

average : (str: String) -> Double
average str = let numWords = wordCount str
                  totalLength = sum (allLengths (words str)) in
                  cast totalLength / cast numWords
    where 
          wordCount : String -> Nat
          wordCount str = length (words str)
          
          allLengths : List String -> List Nat
          allLengths strs = map length strs
        
showAverage : String -> String
showAverage str = cast (average str)

main : IO ()
main = repl "Enter a string: " showAverage

double : Num ty => ty -> ty
double x = x + x

-- more stuff, but not quite as interesting
