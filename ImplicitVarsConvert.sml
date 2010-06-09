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

signature TLU_ImplicitVarsConvert = TOP_LEVEL_UTIL
structure ImplicitVarsConvert :> IMPLICITVARSCONVERT =
struct

open VRef infix ::=
open Syntax infix with'ty with's
open SymbTable
open Context

(* ctx |- B : Type
 * ctx |- X : B
 *)
fun raiseLVar' (ctx, B, S, n) =
	let fun Idx A M n = Eta.etaExpand (fn () => "") (asyncTypeToApx A, Var (M, n), Nil')
		val si = Subst.invert $ Subst.shift 1
		fun invsh ty = TClos (ty, si)
	in case ctx of
		  [] => Atomic' (ImplicitVars.newUCVar B, S)
		| (x, A, SOME INT)::ctx =>
			raiseLVar' (ctx, TLPi' (PBang' (SOME x), TBang' A, B), LApp' (Bang' $ Idx A INT n, S), n+1)
		| (x, A, SOME AFF)::ctx =>
			raiseLVar' (ctx, TLPi' (PAffi' (), TAffi' A, B), LApp' (Affi' $ Idx A AFF n, S), n+1)
		| (x, A, SOME LIN)::ctx =>
			raiseLVar' (ctx, TLPi' (PDown' (), TDown' A, B), LApp' (Down' $ Idx A LIN n, S), n+1)
		| (x, A, NONE)::ctx => raiseLVar' (ctx, invsh B, S, n+1)
	end

fun raiseLVar (Atomic (LogicVar {X, ty, ctx, tag, ...}, ())) = (case (!!X, !ctx) of
	  (SOME _, _) => () (* FIXME: this can never occur?? *)
	| (NONE, NONE) => raise Fail ("Internal error: no context on $"^(Word.toString tag))
	| (NONE, SOME ctx) => X ::= SOME $ normalizeObj $ raiseLVar' (ctx2list ctx, ty, Nil', 1) )
  | raiseLVar _ = ()

(* logicVarsToUCVarsObj : obj -> unit *)
fun logicVarsToUCVarsObj ob = Util.objAppObj raiseLVar ob

(* logicVarsToUCVarsType : asyncType -> unit *)
fun logicVarsToUCVarsType ty = Util.objAppType raiseLVar ty

(* logicVarsToUCVarsKind : kind -> unit *)
fun logicVarsToUCVarsKind ki = Util.objAppKind raiseLVar ki


fun depInc NONE n = n
  | depInc (SOME _) n = n+1

fun uc2xKind lookup n ki = case Kind.prj ki of
	  Type => Type'
	| KPi (x, A, K) => KPi' (x, uc2xType lookup n A, uc2xKind lookup (depInc x n) K)
and uc2xType lookup n ty = case AsyncType.prj ty of
	  TLPi (p, A, B) => TLPi' (p, uc2xSyncType lookup n A, uc2xType lookup (n + nbinds p) B)
	| AddProd (A, B) => AddProd' (uc2xType lookup n A, uc2xType lookup n B)
	| TMonad S => TMonad' (uc2xSyncType lookup n S)
	| TAtomic (a, S) => TAtomic' (a, uc2xTypeSpine lookup n S)
	| TAbbrev aA => TAbbrev' aA
and uc2xTypeSpine lookup n sp = Util.TypeSpineRec.map (uc2xObj lookup n) sp
and uc2xSyncType lookup n sty = case SyncType.prj sty of
	  LExists (p, S1, S2) => LExists' (p, uc2xSyncType lookup n S1, uc2xSyncType lookup (n + nbinds p) S2)
	| TOne => TOne'
	| TDown A => TDown' (uc2xType lookup n A)
	| TAffi A => TAffi' (uc2xType lookup n A)
	| TBang A => TBang' (uc2xType lookup n A)
and uc2xObj lookup n ob = case Obj.prj ob of
	  LLam (p, N) => LLam' (p, uc2xObj lookup (n + nbinds p) N)
	| AddPair (N1, N2) => AddPair' (uc2xObj lookup n N1, uc2xObj lookup n N2)
	| Monad E => Monad' (uc2xExp lookup n E)
	| Atomic (H, S) => Atomic' (uc2xHead lookup n H, uc2xSpine lookup n S)
	| Redex (N, A, S) => Redex' (uc2xObj lookup n N, A, uc2xSpine lookup n S)
	| Constraint (N, A) => Constraint' (uc2xObj lookup n N, uc2xType lookup n A)
and uc2xHead lookup n h = case h of
	  Const c => Const c
	| UCVar v => lookup n v
	| LogicVar X =>
		LogicVar (X with'ty uc2xType lookup (Subst.fold (fn (_,k) => k+1) (fn k => n-k) (#s X)) (#ty X)
			with's Subst.map (normalizeObj o uc2xObj lookup n o unnormalizeObj) (#s X))
	| Var vn => Var vn
and uc2xSpine lookup n sp = Util.SpineRec.map (uc2xMonadObj lookup n) sp
and uc2xExp lookup n e = case ExpObj.prj e of
	  LetRedex (p, S, N, E) => LetRedex' (p, S, uc2xObj lookup n N, uc2xExp lookup (n + nbinds p) E)
	| Let (p, (H, S), E) => Let' (p, (uc2xHead lookup n H, uc2xSpine lookup n S), uc2xExp lookup (n + nbinds p) E)
	| Mon M => Mon' (uc2xMonadObj lookup n M)
and uc2xMonadObj lookup n m = Util.MonadObjRec.map (uc2xObj lookup n) m


fun ctx2Lookup ctx =
	let fun l [] n (x : string) = raise Fail "Internal error: UCVar not in implicits"
		  | l ((y, _)::ys) n x = if x=y then Var (INT, n) else l ys (n+1) x
	in l ctx end

(* convUCVars2VarsKind : implicits -> kind -> kind *)
fun convUCVars2VarsKind imp ki = uc2xKind (ctx2Lookup (rev imp)) 1 ki

(* convUCVars2VarsType : implicits -> asyncType -> asyncType *)
fun convUCVars2VarsType imp ty = uc2xType (ctx2Lookup (rev imp)) 1 ty

(* convUCVars2VarsImps : implicits -> implicits *)
fun convUCVars2VarsImps imp =
	let fun conv [] imps = imps
		  | conv ((x, A)::ctx) imps = conv ctx ((x, uc2xType (ctx2Lookup ctx) 1 A)::imps)
	in conv (rev imp) [] end

(* convUCVars2LogicVarsType : asyncType -> asyncType * (string * obj) list *)
fun convUCVars2LogicVarsType ty =
	let val table = ref $ mapTable (fn A => newLVarCtx (SOME emptyCtx) A) (ImplicitVars.getUCTable ())
		fun uc2lvar n x = case Obj.prj (Clos (valOf (peek (!table, x)), Subst.shift n)) of
			  Atomic (X as LogicVar _, _) => X
			| _ => raise Fail "Internal error: uc2lvar"
		val imps = ImplicitVars.sort ()
		fun convX x = table := insert (!table, x, uc2xObj uc2lvar 0 $ valOf $ peek (!table, x))
		val () = app (convX o #1) imps
	in (uc2xType uc2lvar 0 ty, toList $ !table) end

end
