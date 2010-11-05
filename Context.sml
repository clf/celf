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

signature TLU_Context = TOP_LEVEL_UTIL
structure Context :> CONTEXT =
struct

structure RAList = RandomAccessList

exception ExnCtx of string

datatype mode = INT | AFF | LIN
type cmode = mode option
type 'a context = (string * 'a * cmode) RAList.ralist

fun ctx2list ctx = RAList.toList ctx
fun list2ctx ctx = RAList.fromList ctx
fun ctxCons e ctx = RAList.cons e ctx

fun ctxMap f ctx = RAList.map (fn (x, A, t) => (x, f A, t)) ctx

fun ctxLength ctx = RAList.length ctx

val emptyCtx = RAList.empty

(* ctxIntPart : context -> context *)
fun ctxIntPart ctx =
	let fun d (entry as (_, _, NONE)) = entry
		  | d (entry as (_, _, SOME INT)) = entry
		  | d (x, A, SOME AFF) = (x, A, NONE)
		  | d (x, A, SOME LIN) = (x, A, NONE)
	in RAList.map d ctx end
(* ctxAffPart : context -> context *)
fun ctxAffPart ctx =
	let fun d (entry as (_, _, NONE)) = entry
		  | d (entry as (_, _, SOME INT)) = entry
		  | d (entry as (_, _, SOME AFF)) = entry
		  | d (x, A, SOME LIN) = (x, A, NONE)
	in RAList.map d ctx end

fun use _ (SOME INT) = SOME INT
  | use _ (SOME AFF) = NONE
  | use _ (SOME LIN) = NONE
  | use y NONE = raise ExnCtx ("Linear/affine variable "^y^" occurs in illegal position\n")

(* ctxLookupNum : 'a context * int -> 'a context * mode * 'a *)
(*fun ctxLookupNum (ctx, n) =
	let fun ctxLookup' (i, ctxfront, []) = raise Fail "Internal error: End of context"
		  | ctxLookup' (1, ctxfront, (x, A, f)::ctx) = (* getOpt = valOf because of "use" *)
				(List.revAppend (ctxfront, (x, A, use x f)::ctx), getOpt (f, LIN), A)
		  | ctxLookup' (i, ctxfront, c::ctx) = ctxLookup' (i-1, c::ctxfront, ctx)
	in ctxLookup' (n, [], ctx) end*)
fun ctxLookupNum (ctx, n) =
	let val (x, A, f) = RAList.lookup ctx (n-1)
		val ctxo = if f = SOME INT then ctx else RAList.update ctx (n-1) (x, A, use x f)
	in (ctxo, valOf f, A) end

(* ctxLookupName : 'a context * string -> (int * mode * 'a * 'a context) option *)
fun ctxLookupName (ctx, y) =
	let fun revAppend (xs, l) = foldl (uncurry RAList.cons) l xs
		fun ctxLookup' (i, ctx, NONE) = NONE
		  | ctxLookup' (i, ctxfront, SOME ((x, A, f), ctx)) = (* getOpt = valOf because of "use" *)
				if x=y then SOME (i, getOpt (f, LIN), A,
									revAppend ((x, A, use x f)::ctxfront, ctx))
				else ctxLookup' (i+1, (x, A, f)::ctxfront, RAList.prj ctx)
	in ctxLookup' (1, [], RAList.prj ctx) end

(* ctxPush : string * mode * 'a * 'a context -> 'a context *)
fun ctxPush (x, m, A, ctx) = RAList.cons (x, A, SOME m) ctx

(* ctxPushNO : 'a * 'a context -> 'a context *)
fun ctxPushNO (A, ctx) = RAList.cons ("", A, NONE) ctx

(* ctxCondPushINT : string option * 'a * 'a context -> 'a context *)
fun ctxCondPushINT (NONE, _, ctx) = ctx
  | ctxCondPushINT (SOME x, A, ctx) = ctxPush (x, INT, A, ctx)

(* ctxPop : 'a context -> 'a context *)
fun ctxPop c = case RAList.prj c of
	  SOME ((_, _, NONE), ctx) => ctx
	| SOME ((_, _, SOME INT), ctx) => ctx
	| SOME ((_, _, SOME AFF), ctx) => ctx
	| SOME ((x, _, SOME LIN), ctx) => raise ExnCtx ("Linear variable "^x^" doesn't occur\n")
	| NONE => raise Fail "Internal error ctxPop: empty context"

fun addJoin ((x, A, f1), (_, _, f2)) =
	let val joinerr = "Contexts can't join: linear variable "^x^" only occurs on one side\n"
		val f = case (f1, f2) of
				  (NONE, NONE) => NONE
				| (NONE, SOME LIN) => raise ExnCtx joinerr
				| (SOME LIN, NONE) => raise ExnCtx joinerr
				| (NONE, SOME AFF) => NONE
				| (SOME AFF, NONE) => NONE
				| (SOME INT, SOME INT) => SOME INT
				| (SOME AFF, SOME AFF) => SOME AFF
				| (SOME LIN, SOME LIN) => SOME LIN
				| _ => raise Fail "Internal error: context misalignment"
	in (x, A, f) end

(* ctxAddJoin : 'a context * 'a context -> 'a context *)
fun ctxAddJoin ctxs = RAList.pairMapEq addJoin ctxs

fun joinAffLin ((x, A, f1), (_, _, f2)) =
	let val f = case (f1, f2) of
				  (NONE, NONE) => NONE
				| (NONE, SOME LIN) => SOME LIN
				| (NONE, SOME AFF) => NONE
				| (SOME AFF, SOME AFF) => SOME AFF
				| (SOME INT, SOME INT) => SOME INT
				| (SOME AFF, NONE) => SOME AFF
				| _ => raise Fail "Internal error joinAffLin: context misalignment"
	in (x, A, f) end

(* ctxJoinAffLin : 'a context * 'a context -> 'a context *)
(* if  AffPart(G1)=G1  then  ctxJoinAffLin (G1, G2) = G1+LinPart(G2) *)
fun ctxJoinAffLin ctxs = RAList.pairMapEq joinAffLin ctxs

end
