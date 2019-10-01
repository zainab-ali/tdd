module overview

main : IO ()
main = putStrLn (cast 'x')

StringOrInt : Bool -> Type
StringOrInt True = Int
StringOrInt False = String

getStringOrInt : (x : Bool) -> StringOrInt x
getStringOrInt x = case x of
                   True => 94
                   False => "Nintey four"

valToString : (x: Bool) -> (StringOrInt x) -> String
valToString x val = case x of
                    True => cast val
                    False => val

