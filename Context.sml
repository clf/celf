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

structure Context :> CONTEXT =
struct

exception ExnCtx of string

datatype mode = INT | LIN
type cmode = mode option
type 'a context = (string * 'a * cmode) list

fun ctx2list ctx = ctx
fun ctxCons e ctx = e::ctx

fun ctxMap f ctx = map (fn (x, A, t) => (x, f A, t)) ctx

val emptyCtx = []

(* ctxDelLin : context -> context *)
fun ctxDelLin ctx =
	let fun delLin' (entry as (_, _, SOME INT)) = entry
		  | delLin' (entry as (_, _, NONE)) = entry
		  | delLin' (x, A, SOME LIN) = (x, A, NONE)
	in map delLin' ctx end

fun use _ (SOME INT) = SOME INT
  | use _ (SOME LIN) = NONE
  | use y NONE = raise Fail ("Linear variable "^y^" can't be used twice/here\n")

(* ctxLookupNum : 'a context * int -> 'a context * mode * 'a *)
fun ctxLookupNum (ctx, n) =
	let fun ctxLookup' (i, ctxfront, []) = raise Fail "Internal error: End of context\n"
		  | ctxLookup' (1, ctxfront, (x, A, f)::ctx) =
				(List.revAppend (ctxfront, (x, A, use x f)::ctx), getOpt (f, LIN), A)
		  | ctxLookup' (i, ctxfront, c::ctx) = ctxLookup' (i-1, c::ctxfront, ctx)
	in ctxLookup' (n, [], ctx) end

(* ctxLookupName : 'a context * string -> (int * mode * 'a * 'a context) option *)
fun ctxLookupName (ctx, y) =
	let fun ctxLookup' (i, ctx, []) = NONE
		  | ctxLookup' (i, ctxfront, (x, A, f)::ctx) =
				if x=y then SOME (i, getOpt (f, LIN), A,
									List.revAppend (ctxfront, (x, A, use x f)::ctx))
				else ctxLookup' (i+1, (x, A, f)::ctxfront, ctx)
	in ctxLookup' (1, [], ctx) end

(* ctxPushINT : string * 'a * 'a context -> 'a context *)
fun ctxPushINT (x, A, ctx) = (x, A, SOME INT) :: ctx

(* ctxCondPushINT : string option * 'a * 'a context -> 'a context *)
fun ctxCondPushINT (NONE, _, ctx) = ctx
  | ctxCondPushINT (SOME x, A, ctx) = ctxPushINT (x, A, ctx)

(* ctxPushLIN : string * 'a * 'a context -> 'a context *)
fun ctxPushLIN (x, A, ctx) = (x, A, SOME LIN) :: ctx

(* ctxPopINT : 'a context -> 'a context *)
fun ctxPopINT ((_, _, SOME INT)::ctx) = ctx
  | ctxPopINT _ = raise Fail "Internal error: ctxPopINT"

(* ctxPopLIN : bool * 'a context -> 'a context *)
fun ctxPopLIN (_, (_, _, NONE)::ctx) = ctx
  | ctxPopLIN (true, (_, _, SOME LIN)::ctx) = ctx
  | ctxPopLIN (false, (x, _, SOME LIN)::ctx) = raise ExnCtx (x^" doesn't occur\n")
  | ctxPopLIN _ = raise Fail "Internal error: ctxPopLIN"

(* ctxPopLINopt : bool * 'a context -> 'a context option *)
fun ctxPopLINopt tCtx = SOME (ctxPopLIN tCtx) handle ExnCtx _ => NONE

fun addJoin (t1, t2) ((x, A, f1), (_, _, f2)) =
	let val f = case (t1, f1, t2, f2) of
					(_, SOME INT, _, SOME INT) => SOME INT
				  | (_, NONE, _, NONE) => NONE
				  | (_, SOME LIN, _, SOME LIN) => SOME LIN
				  | (_, NONE, true, SOME LIN) => NONE
				  | (_, NONE, false, SOME LIN) => raise ExnCtx "Contexts can't join\n"
				  | (true, SOME LIN, _, NONE) => NONE
				  | (false, SOME LIN, _, NONE) => raise ExnCtx "Contexts can't join\n"
				  | _ => raise Fail "Internal error: context misalignment\n"
	in (x, A, f) end

fun mapEq f ([], []) = []
  | mapEq f (x::xs, y::ys) = f (x, y) :: mapEq f (xs, ys)
  | mapEq _ _ = raise Fail "Unequal lengths"
(* ctxAddJoin : bool * bool -> 'a context * 'a context -> 'a context *)
fun ctxAddJoin topFlags ctxs = (*ListPair.*)mapEq (addJoin topFlags) ctxs

(* ctxAddJoinOpt : bool * bool -> 'a context * 'a context -> 'a context option *)
fun ctxAddJoinOpt topFlags ctxs = SOME (ctxAddJoin topFlags ctxs) handle ExnCtx _ => NONE

end
