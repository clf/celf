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

functor WhnfFun (Syn : SYNTAX_CORE2) : WHNF =
struct

structure Syn = Syn
open Syn

fun whnfObj N = whnfObjP (Obj.prj N)

and whnfObjP (Redex (N, _, S)) = whnfRedex (N, S)
  | whnfObjP (Constraint (N, _)) = whnfObj N
  | whnfObjP (LinLam xN) = NfLinLam xN
  | whnfObjP (Lam xN) = NfLam xN
  | whnfObjP (AddPair N1N2) = NfAddPair N1N2
  | whnfObjP Unit = NfUnit
  | whnfObjP (Monad E) = NfMonad E
  | whnfObjP (Atomic hS) = NfAtomic hS

and whnfRedex (ob, sp) = case (Obj.prj ob, Spine.prj sp) of
	  (N, Nil) => whnfObjP N
	| (LinLam (_, N1), LinApp (N2, S)) => whnfRedex (Clos (N1, Subst.subL N2), S)
	| (Lam (_, N1), App (N2, S)) => whnfRedex (Clos (N1, Subst.subI N2), S)
	| (AddPair (N, _), ProjLeft S) => whnfRedex (N, S)
	| (AddPair (_, N), ProjRight S) => whnfRedex (N, S)
	| (Atomic (H, S1), S2) => NfAtomic (H, appendSpine (S1, Spine.inj S2))
	| (Redex (N, A, S1), S2) => whnfRedex (N, appendSpine (S1, Spine.inj S2))
	| (Constraint (N, A), S) => whnfRedex (N, Spine.inj S)
	| _ => raise Fail "Internal error: whnfRedex\n"


fun whnfExp e = whnfExpP (ExpObj.prj e)
and whnfExpP (Mon M) = Mon M
  | whnfExpP (Let (p, N, E)) =
		(case whnfObj N of
			  NfMonad E' =>
				(case ExpObj.prj E' of
					  Mon M => whnfExp (whnfLetRedex (p, M, E))
					| Let (q, N', E'') =>
							whnfExpP (Let (q, N',
								Let' (PClos (p, Subst.shift (nbinds q)), Monad' E'',
								EClos (E, Subst.dotn (nbinds p) (Subst.shift (nbinds q)))))))
			| NfAtomic hS => Let (p, hS, E)
			| _ => raise Fail "Internal error: whnfMonObj\n")
and whnfLetRedex (p, M, E) = case (Pattern.prj p, MonadObj.prj M) of
	  (PTensor (p1, p2), Tensor (M1, M2)) =>
			(* p2 should be PClos(p2,nbinds p1) in the redex below, but
			   it doesn't matter since the types are not considered *)
			whnfLetRedex (p1, M1, whnfLetRedex (p2, MClos (M2, Subst.shift (nbinds p1)), E))
	| (POne, One) => E
	| (PDepPair (x, _, p1), DepPair (N, M1)) => EClos (whnfLetRedex (p1, M1, E), Subst.subI N)
	| (PVar (x, _), Norm N) => EClos (E, Subst.subL N)
	| _ => raise Fail "Internal error: whnfLetRedex\n"


(*
val whnfLetSpine = ExpObjAuxDefs.unfold whnfExp

val normalizeKind = Util.objExpMapKind whnfExp whnfObj
val normalizeType = Util.objExpMapType whnfExp whnfObj
val normalizeObj = Util.objExpMapObj whnfExp whnfObj
*)

end
