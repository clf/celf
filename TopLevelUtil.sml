datatype ('a, 'b) sum = INL of 'a | INR of 'b
infixr 1 $
fun f $ x = f x
