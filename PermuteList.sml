structure PermuteList :> PERMUTELIST =
struct

datatype 'a permuteList = Perm of 'a list | Append of 'a permuteList * 'a permuteList

val rndState = Random.rand (42, 117)
fun rndBool () = Random.randReal rndState < 0.5

(* fromList : a' list -> 'a permuteList *)
fun fromList l = Perm l

fun part l = case List.partition (rndBool o ignore) l of
		  ([], l) => part l
		| (l, []) => part l
		| (l1, l2) => Append (Perm l1, Perm l2)

(* prj : 'a permuteList -> ('a * 'a permuteList) option *)
fun prj (Append (Append (l1, l2), l3)) = prj (Append (l1, Append (l2, l3)))
  | prj (Append (l1, l2)) =
		(case prj l1 of
			  NONE => prj l2
			| SOME (a, l1') => SOME (a, Append (l1', l2)))
  | prj (Perm []) = NONE
  | prj (Perm [a]) = SOME (a, Perm [])
  | prj (Perm [a1, a2]) = if rndBool () then SOME (a1, Perm [a2]) else SOME (a2, Perm [a1])
  | prj (Perm l) = prj (part l)

(* findSome : ('a -> 'b option) -> 'a permuteList -> 'b option *)
fun findSome f = Option.composePartial (fn (x, xs) =>
		let val fx = f x in if isSome fx then fx else findSome f xs end, prj)

end
