(*  Celf
 *  Copyright (C) 2008 Anders Schack-Nielsen and Carsten Schürmann
 *
 *  This file is part of Celf.
 *
 *  Celf is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  Celf is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with Celf.  If not, see <http://www.gnu.org/licenses/>.
 *)

structure PermuteList :> PERMUTELIST =
struct

datatype 'a permuteList = Perm of 'a list | Append of 'a permuteList * 'a permuteList

(* mlkit bug workaround : inline composePartial *)
fun composePartial (f, g) x =
	case g x of
		  NONE => NONE
		| SOME y => f y

(* random generator *)
val rndState = ref (Rnd.rndNew 117)
fun setSeed seed = rndState := Rnd.rndNew seed
fun rndBool () = Rnd.rndReal (!rndState) < 0.5

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
fun findSome f = composePartial (fn (x, xs) =>
		let val fx = f x in if isSome fx then fx else findSome f xs end, prj)

end
