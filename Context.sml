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

(*datatype mode = INT | AFF | LIN
datatype cmode = NOINT | NOAFF | M of mode*)
datatype mode = INT | AFF | LIN
type cmode = mode option
type 'a context = (string * 'a * cmode) list

fun ctx2list ctx = ctx
fun ctxCons e ctx = e::ctx

fun ctxMap f ctx = map (fn (x, A, t) => (x, f A, t)) ctx

val emptyCtx = []

(* ctxIntPart : context -> context *)
fun ctxIntPart ctx =
	let fun d (entry as (_, _, NONE)) = entry
		  | d (entry as (_, _, SOME INT)) = entry
		  | d (x, A, SOME AFF) = (x, A, NONE)
		  | d (x, A, SOME LIN) = (x, A, NONE)
	in map d ctx end
(* ctxAffPart : context -> context *)
fun ctxAffPart ctx =
	let fun d (entry as (_, _, NONE)) = entry
		  | d (entry as (_, _, SOME INT)) = entry
		  | d (entry as (_, _, SOME AFF)) = entry
		  | d (x, A, SOME LIN) = (x, A, NONE)
	in map d ctx end

fun use _ (SOME INT) = SOME INT
  | use _ (SOME AFF) = NONE
  | use _ (SOME LIN) = NONE
  | use y NONE = raise Fail ("Linear/affine variable "^y^" can't be used twice/here\n")

(* ctxLookupNum : 'a context * int -> 'a context * mode * 'a *)
fun ctxLookupNum (ctx, n) =
	let fun ctxLookup' (i, ctxfront, []) = raise Fail "Internal error: End of context\n"
		  | ctxLookup' (1, ctxfront, (x, A, f)::ctx) = (* getOpt = valOf because of "use" *)
				(List.revAppend (ctxfront, (x, A, use x f)::ctx), getOpt (f, LIN), A)
		  | ctxLookup' (i, ctxfront, c::ctx) = ctxLookup' (i-1, c::ctxfront, ctx)
	in ctxLookup' (n, [], ctx) end

(* ctxLookupName : 'a context * string -> (int * mode * 'a * 'a context) option *)
fun ctxLookupName (ctx, y) =
	let fun ctxLookup' (i, ctx, []) = NONE
		  | ctxLookup' (i, ctxfront, (x, A, f)::ctx) = (* getOpt = valOf because of "use" *)
				if x=y then SOME (i, getOpt (f, LIN), A,
									List.revAppend (ctxfront, (x, A, use x f)::ctx))
				else ctxLookup' (i+1, (x, A, f)::ctxfront, ctx)
	in ctxLookup' (1, [], ctx) end

(* ctxPush : string * mode * 'a * 'a context -> 'a context *)
fun ctxPush (x, m, A, ctx) = (x, A, SOME m) :: ctx

(* ctxPushNO : 'a * 'a context -> 'a context *)
fun ctxPushNO (A, ctx) = ("", A, NONE) :: ctx

(* ctxCondPushINT : string option * 'a * 'a context -> 'a context *)
fun ctxCondPushINT (NONE, _, ctx) = ctx
  | ctxCondPushINT (SOME x, A, ctx) = ctxPush (x, INT, A, ctx)

(* ctxPop : 'a context -> 'a context *)
fun ctxPop ((_, _, NONE)::ctx) = ctx
  | ctxPop ((_, _, SOME INT)::ctx) = ctx
  | ctxPop ((_, _, SOME AFF)::ctx) = ctx
  | ctxPop ((x, _, SOME LIN)::ctx) = raise ExnCtx (x^" doesn't occur\n")
  | ctxPop [] = raise Fail "Internal error ctxPop: empty context"

(* ctxPopLINopt : 'a context -> 'a context option *)
fun ctxPopLINopt ctx = SOME (ctxPop ctx) handle ExnCtx _ => NONE

fun addJoin ((x, A, f1), (_, _, f2)) =
	let val f = case (f1, f2) of
				  (NONE, NONE) => NONE
				| (NONE, SOME LIN) => raise ExnCtx "Contexts can't join\n"
				| (SOME LIN, NONE) => raise ExnCtx "Contexts can't join\n"
				| (NONE, SOME AFF) => NONE
				| (SOME AFF, NONE) => NONE
				| (SOME INT, SOME INT) => SOME INT
				| (SOME AFF, SOME AFF) => SOME AFF
				| (SOME LIN, SOME LIN) => SOME LIN
				| _ => raise Fail "Internal error: context misalignment\n"
	in (x, A, f) end

fun mapEq f ([], []) = []
  | mapEq f (x::xs, y::ys) = f (x, y) :: mapEq f (xs, ys)
  | mapEq _ _ = raise Fail "Unequal lengths"
(* ctxAddJoin : 'a context * 'a context -> 'a context *)
fun ctxAddJoin ctxs = (*ListPair.*)mapEq addJoin ctxs

(* ctxAddJoinOpt : 'a context * 'a context -> 'a context option *)
fun ctxAddJoinOpt ctxs = SOME (ctxAddJoin ctxs) handle ExnCtx _ => NONE

fun joinAffLin ((x, A, f1), (_, _, f2)) =
	let val f = case (f1, f2) of
				  (NONE, NONE) => NONE
				| (NONE, SOME LIN) => SOME LIN
				| (NONE, SOME AFF) => NONE
				| (SOME AFF, SOME AFF) => SOME AFF
				| (SOME INT, SOME INT) => SOME INT
				| _ => raise Fail "Internal error joinAffLin: context misalignment\n"
	in (x, A, f) end

(* ctxJoinAffLin : 'a context * 'a context -> 'a context *)
fun ctxJoinAffLin ctxs = (*ListPair.*)mapEq joinAffLin ctxs

end
