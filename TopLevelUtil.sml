datatype ('a, 'b) sum = INL of 'a | INR of 'b
infixr 1 $
fun f $ x = f x
(* val map1 : ('a -> 'c) -> 'a * 'b -> 'c * 'b
 * val map2 : ('b -> 'd) -> 'a * 'b -> 'a * 'd
 * val map12 : ('a -> 'c) -> ('b -> 'd) -> 'a * 'b -> 'c * 'd
 *)
fun map1 f (a, b) = (f a, b)
fun map2 f (a, b) = (a, f b)
fun map12 f g (a, b) = (f a, g b)
fun listPairMapEq f ([], []) = []
  | listPairMapEq f (x::xs, y::ys) = f (x, y) :: listPairMapEq f (xs, ys)
  | listPairMapEq _ _ = raise Fail "Unequal lengths"
fun curry f x y = f (x, y)
fun uncurry f (x, y) = f x y

(* empty signature used to generate a depency in the compilation manager *)
signature TOP_LEVEL_UTIL = sig end
