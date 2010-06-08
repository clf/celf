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

structure BackTrack :> BACKTRACK =
struct

datatype trailPoint = Mark | Update of unit -> unit (*| Assign of Syntax.obj option ref*)

val nMarks = ref 0
val trail : trailPoint list ref = ref []

fun push tp = trail := tp :: (!trail)
fun pop () = hd (!trail) before trail := tl (!trail)

fun setMark () = (push Mark; nMarks := 1 + !nMarks)
fun mark () = !nMarks before setMark ()

fun rewind () = case pop () of
	  Mark => nMarks := !nMarks - 1
	| Update undoF => (undoF (); rewind ())
	(*| Assign r => (r := NONE; rewind ())*)

fun eraseMarks' 0 tacc t = trail := List.revAppend (tacc, t)
  | eraseMarks' n tacc (Mark::t) = eraseMarks' (n-1) tacc t
  | eraseMarks' n tacc (tp::t) = eraseMarks' n (tp::tacc) t
  | eraseMarks' _ _ [] = raise Fail "Internal error: eraseMarks'"

fun eraseMarks n = (eraseMarks' (!nMarks - n) [] (!trail); nMarks := n)


(* trailAssign : obj option ref -> unit *)
(* trails the assignment of the ref cell for future backtracking *)
(*fun trailAssign r = push (Assign r)*)

(* trailUpdate : (unit -> unit) -> unit *)
(* trails a state update and saves the undo function for future backtracking *)
fun trailUpdate undoF = if !nMarks <> 0 then push (Update undoF) else ()

(* backtrackC : (('a -> exn) -> unit) -> 'a option *)
(* backtrackC f
 * run "f commitExn", then backtrack updates done by f unless
 * commitExn x has been raised in which case we erase the backtracking 
 * marks and return SOME x.
 *)
fun backtrackC f =
	let exception commitExn of 'a
		val n = mark ()
	in
		(f commitExn; rewind (); NONE) handle commitExn x => (eraseMarks n; SOME x)
	end

(* backtrack : (unit -> unit) -> unit *)
(* val backtrack f = let val NONE = backtrackC (fn _ => f ()) in () end *)
fun backtrack f =
	( mark ()
(*	; if !nMarks mod 1000 = 0 then print ("["^Int.toString (!nMarks)^"]") else ()*)
	; f ()
	; rewind () )

end
