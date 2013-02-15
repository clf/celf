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
type 'a permuteList = 'a list

fun setSeed seed = ()
fun fromList l = l
fun prj (H :: T) = SOME (H, T)
  | prj nil = NONE

fun findSome f = Option.composePartial (fn (x, xs) =>
		let val fx = f x in if isSome fx then fx else findSome f xs end, prj)

(* forAll : ('a -> unit) -> 'a permuteList -> unit *)
fun forAll f l = Option.app (fn (x, xs) => (f x ; forAll f xs)) (prj l)

end
