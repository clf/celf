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

signature TLU_PrettyPrint = TOP_LEVEL_UTIL
structure PrettyPrint :> PRETTYPRINT =
struct

open Syntax

val printImpl = ref false

fun join' [] = []
  | join' [x] = x
  | join' (x::xs) = x @ ["] ["] @ join' xs
val join = (fn [] => [] | xs => ["[["] @ xs @ ["]]"]) o join'

fun paren false x = x
  | paren true x = ["("] @ x @ [")"]

fun lookup (x::ctx) 1 = x
  | lookup (_::ctx) n = lookup ctx (n-1)
  | lookup [] n = Int.toString n (*raise Fail "Internal error: de Bruijn index out of range\n"*)

fun add x ctx =
	let fun eq (x : string) y = x=y
(*		fun add' x = if List.exists (eq x) ctx then add' (x^"'") else (x, x::ctx)*)
		fun add1 n x =
			let val tryname = x ^ Int.toString n
			in if List.exists (eq tryname) ctx then add1 (n+1) x else (tryname, tryname::ctx) end
		fun add' x = if List.exists (eq x) ctx then add1 1 (x^"_") else (x, x::ctx)
	in if x="" then add1 1 "X" else add' x end

val noSkip = ref false
fun getImplLength c = if !noSkip then 0 else Signatur.getImplLength c

fun pKind ctx ki = case Kind.prj ki of
	  Type => ["type"]
	| KPi (NONE, A, K) => pType ctx true A @ [" -> "] @ pKind ctx K
	| KPi (SOME x, A, K) =>
			let val (x', ctx') = add x ctx
			in ["Pi "^x'^": "] @ pType ctx false A @ [". "] @ pKind ctx' K end
and pType ctx pa ty = if isUnknown ty then ["???"] else case AsyncType.prj ty of
	  Lolli (A, B) => paren pa (pType ctx true A @ [" -o "] @ pType ctx false B)
	| TPi (NONE, A, B) => paren pa (pType ctx true A @ [" -> "] @ pType ctx false B)
	| TPi (SOME x, A, B) =>
			let val (x', ctx') = add x ctx
			in paren pa (["Pi "^x'^": "] @ pType ctx false A @ [". "]
					@ pType ctx' false B) end
	| AddProd (A, B) => paren pa (pType ctx true A @ [" & "] @ pType ctx true B)
	| Top => ["<T>"]
	| TMonad S => ["{"] @ pSyncType ctx false S @ ["}"]
	| TAtomic (a, S) => (*(fn (a', []) => a' | (a', ts) => paren pa (a' @ ts)) ([a] @ join (map (pObj ctx true) impl), pTypeSpine ctx S)*)
			[a] @ (*join (map (pObj ctx false) impl) @*) pTypeSpineSkip ctx S (getImplLength a)
	| TAbbrev (a, ty) => [a]
and pTypeSpineSkip ctx sp n = if n=0 then pTypeSpine ctx sp else case TypeSpine.prj sp of
	  TNil => raise Fail "Internal error: pTypeSpineSkip\n"
	| TApp (N, S) =>
		(if !printImpl then [" <"] @ pObj ctx false N @ [">"] else [])
		@ pTypeSpineSkip ctx S (n-1)
and pTypeSpine ctx sp = case TypeSpine.prj sp of
	  TNil => []
	| TApp (N, S) => [" "] @ pObj ctx true N @ pTypeSpine ctx S
and pSyncType ctx pa sty = case SyncType.prj sty of
	  TTensor (S1, S2) => paren pa (pSyncType ctx true S1 @ [" * "] @ pSyncType ctx true S2)
	| TOne => ["1"]
	| Exists (x, A, S) =>
			let val (x', ctx') = case x of NONE => ("!", ctx) | SOME x => add x ctx
			in paren pa (["Exists "^x'^": "] @ pType ctx false A @ [". "]
					@ pSyncType ctx' false S) end
	| Async A => pType ctx pa A
and pObj ctx pa ob = case Obj.prj ob of
	  LinLam (x, N) =>
			let val (x', ctx') = add x ctx
			in paren pa (["\\^ "^x'^". "] @ pObj ctx' false N) end
	| Lam (x, N) =>
			let val (x', ctx') = add x ctx
			in paren pa (["\\ "^x'^". "] @ pObj ctx' false N) end
	| AddPair (N1, N2) => ["<"] @ pObj ctx false N1 @ [", "] @ pObj ctx false N2 @ [">"]
	| Unit => ["<>"]
	| Monad E => ["{"] @ pExp ctx E @ ["}"]
	| Atomic (H, S) =>
			let val skip = case H of Const c => getImplLength c | _ => 0
			in case (pHead ctx H, pSpineSkip ctx S skip) of
				  (h, []) => h
				| (h, s) => paren pa (h @ s)
			end
	| Redex (N, _, S) =>
			(fn [] => pObj ctx pa N | s => paren pa (pObj ctx true N @ s)) (pSpine ctx S)
	| Constraint (N, A) => pObj ctx pa N
and pHead ctx h = case h of
	  Const c => [c] (*@ join (map (pObj ctx false) impl)*)
	| Var n => [lookup ctx n] (*[Int.toString n]*)
	| UCVar v => ["#"^v]
	| LogicVar {ty, s, ctx=ref G, tag, ...} =>
		["$", Word.toString tag]
		(*@ ["<"] @ pContext ctx G @ [", "] @ pType ctx false (TClos (ty, s)) @ [">"]*)
		@ [Subst.substToStr (String.concat o (pObj ctx true)) s]
and pContext ctx NONE = ["--"]
  | pContext ctx (SOME G) = join (map (pType ctx false o #2) (Context.ctx2list G))
and pSpineSkip ctx sp n = if n=0 then pSpine ctx sp else case Spine.prj sp of
	  App (N, S) =>
		(if !printImpl then [" <"] @ pObj ctx false N @ [">"] else [])
		@ pSpineSkip ctx S (n-1)
	| _ => raise Fail "Internal error: pSpineSkip\n"
and pSpine ctx sp = case Spine.prj sp of
	  Nil => []
	| App (N, S) => [" "] @ pObj ctx true N @ pSpine ctx S
	| LinApp (N, S) => [" ^ "] @ pObj ctx true N @ pSpine ctx S
	| ProjLeft S => [" pi_1"] @ pSpine ctx S
	| ProjRight S => [" pi_2"] @ pSpine ctx S
and pExp ctx e = case ExpObj.prj e of
	  Let (p, N, E) =>
			let val (pP, ctx') = pPattern ctx ctx false p
			in ["\n    let {"] @ pP @ ["} = "] @ pObj ctx false N @ [" in "] @ pExp ctx' E end
	| Mon M => pMonadObj ctx false M
and pMonadObj ctx pa m = case MonadObj.prj m of
	  Tensor (M1, M2) => paren pa (pMonadObj ctx true M1 @ [" * "] @ pMonadObj ctx true M2)
	| One => ["1"]
	| DepPair (N, M) => ["["] @ pObj ctx false N @ [", "] @ pMonadObj ctx false M @ ["]"]
	| Norm N => pObj ctx pa N
and pPattern ctx bctx pa p = case Pattern.prj p of
	  PTensor (p1, p2) =>
			let val (pP1, bctx') = pPattern ctx bctx true p1
				val (pP2, bctx'') = pPattern ctx bctx' true p2
			in (paren pa (pP1 @ [" * "] @ pP2), bctx'') end
	| POne => (["1"], bctx)
	| PDepPair (x, A, p) =>
			let val (x', bctx') = add x bctx
				val (x'', ctx') = add x' ctx
				val () = if x' = x'' then () else raise Fail "Internal error: pPattern\n"
				val (pP, bctx'') = pPattern ctx' bctx' false p
			in (["["^x'^": "] @ pType ctx false A @ [", "] @ pP @ ["]"], bctx'') end
	| PVar (x, A) =>
			let val (x', bctx') = add x bctx
			in ([x'^": "] @ pType ctx false A, bctx') end

val printKind = String.concat o (pKind [])
val printType = String.concat o (pType [] false)
val printObj = String.concat o (pObj [] false)

fun printPreType ty = ( noSkip := true; printType ty before noSkip := false )
fun printPreObj ob = ( noSkip := true; printObj ob before noSkip := false )

end
