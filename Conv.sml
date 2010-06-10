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

(* Convertibility among CLF terms and types *)
(* Author: Carsten Schuermann *)
(* Walked: Oct 18, 12:00 *)

structure Conv :> CONV =
struct

(* All objects, types, spines, patterns, expressions and monadic objects are
   assumed to be well-typed and in normal form  *)

open Syntax

exception ExnConv of string

(* Invariant:  convAsyncType (ty1, ty2) => ()
 * if  G |- ty1 == ty2 : kind
 * otherwise ExnConv is raised
 *)
fun convAsyncType (ty1, ty2) = case (Util.nfTypePrjAbbrev ty1, Util.nfTypePrjAbbrev ty2) of
	  (TLPi (_, A1, B1), TLPi (_, A2, B2)) => (convSyncType (A1, A2); convAsyncType (B1, B2))
	| (AddProd (A1, B1), AddProd (A2, B2)) => (convAsyncType (A1, A2); convAsyncType (B1, B2))
	| (TAtomic (a1, TS1), TAtomic (a2, TS2)) =>
		if (a1 = a2) then convTypeSpine (TS1, TS2)
		else raise ExnConv "Convertibility: Type Clash"
	| (TMonad S1, TMonad S2) => convSyncType (S1, S2)
	| _ => raise ExnConv "Convertibility: Types differ"


(* Invariant:  convTypeSpine (TS1, TS2) => ()
 * if  G |- TS1 == TS2 : K1 > K2
 * otherwise ExnConv is raised
 *)
and convTypeSpine (ts1, ts2) = case (NfTypeSpine.prj ts1, NfTypeSpine.prj ts2) of
	  (TNil, TNil) => ()
	| (TApp (M1, TS1), TApp (M2, TS2)) => (convObj (M1, M2); convTypeSpine (TS1, TS2))
	| _ => raise ExnConv "Convertibility"

and convSyncType (st1, st2) = case (NfSyncType.prj st1, NfSyncType.prj st2) of
	  (LExists (_, S1, T1), LExists (_, S2, T2)) => (convSyncType (S1, S2); convSyncType (T1, T2))
	| (TOne, TOne) => ()
	| (TDown A1, TDown A2) => convAsyncType (A1, A2)
	| (TAffi A1, TAffi A2) => convAsyncType (A1, A2)
	| (TBang A1, TBang A2) => convAsyncType (A1, A2)
	| _ => raise ExnConv "Convertibility: SyncTypes differ"

(* Invariant:  convObj (N1, N2) => ()
 * if  G |- N1 == N2 : A
 * otherwise ExnConv is raised
 *)
and convObj (ob1, ob2) = case (NfObj.prj ob1, NfObj.prj ob2) of
	  (NfLLam (_, N), NfLLam (_, M)) => convObj (N, M)
	| (NfAddPair (N1, N2), NfAddPair (M1, M2)) => (convObj (N1, M1); convObj (N2, M2))
	| (NfMonad E1, NfMonad E2) => convExpObj (E1, E2)
	| (NfAtomic (H1, S1), NfAtomic (H2, S2)) => (convHead (H1, H2); convSpine (S1, S2))
	| _ => raise ExnConv ("Error in convertibilty of "^PrettyPrint.printObj (unnormalizeObj ob1)
				^" and "^PrettyPrint.printObj (unnormalizeObj ob2))


(* Invariant:  convHead (H1, H2) => ()
 * if  G |- H1 == H2 : A
 * otherwise ExnConv is raised
 *)
and convHead (hd1, hd2) = case (hd1, hd2) of
	  (Const c1, Const c2) =>
		if c1 = c2 then ()
		else raise ExnConv "Convertibilty failed: Head mismatch"
	| (Var n1, Var n2) =>
		if n1 = n2 then ()
		else raise ExnConv "Convertibilty failed: Bound variable clash"
	| (LogicVar {X=r1, s=s1, ...}, LogicVar {X=r2, s=s2, ...}) =>
		if VRef.eq (r1, r2) then () (* FIXME: convSub (s1, s2) assumed *)
		else raise ExnConv "Convertibilty failed: Distinct logic variables"
	| _ => raise ExnConv "Convertibility failed"


(* Invariant:  convSpine (S1, S2) => ()
 * if  G |- S1 == S2 : A1 > A2
 * otherwise ExnConv is raised
 *)
and convSpine (sp1, sp2) = case (NfSpine.prj sp1, NfSpine.prj sp2) of
	  (Nil, Nil) => ()
	| (LApp (M1, S1), LApp (M2, S2)) => (convMonadObj (M1, M2); convSpine (S1, S2))
	| (ProjLeft S1, ProjLeft S2) => convSpine (S1, S2)
	| (ProjRight S1, ProjRight S2) => convSpine (S1, S2)
	| _ => raise ExnConv "Convertibility failed"


(* Invariant:  convMonadObj (M1, M2) => ()
 * if  G |- M1 == M2 : S
 * otherwise ExnConv is raised
 *)
and convMonadObj (M1, M2) = case (NfMonadObj.prj M1, NfMonadObj.prj M2) of
	  (DepPair (M11, M12), DepPair (M21, M22)) =>
		(convMonadObj (M11, M21); convMonadObj (M12, M22))
	| (One, One) => ()
	| (Down N1, Down N2) => convObj (N1, N2)
	| (Affi N1, Affi N2) => convObj (N1, N2)
	| (Bang N1, Bang N2) => convObj (N1, N2)
	| (MonUndef, _) => raise Fail "Internal error: convMonadObj: MonUndef"
	| (_, MonUndef) => raise Fail "Internal error: convMonadObj: MonUndef"
	| _ => raise ExnConv "Convertibility failed"


(* Invariant:  convExpObj (E1, E2)  => ()
 * if  G |- let P11 = R11 in ... let P1n = R1n in E1
 *          == let P21 = R21 in ... let P2n = R2n in E2 : S
 * otherwise ExnConv is raised
 * where n = |C1| = |C2|
 * and   Ci = ((Pi1, Ri1), ..., (Pin, Rin))
 *)
and convExpObj (E1, E2) = case (NfExpObj.prj E1, NfExpObj.prj E2) of
	  (NfMon M1, NfMon M2) => convMonadObj (M1, M2)
	| (NfLet (P1, R1, E1'), NfLet (P2, R2, E2')) =>
		convExpObj (E1', convExpObj1 (E1, E2))
	| _ => raise ExnConv "Convertibility failed"


(* Invariant:
 * If    G |- E1 == let P1=R1 in E1' : S
 * and   G |- E2 : S
 * then  there exists E, such that
 * and   G, P1 |- E = convExpObj1 (E1, E2) : S
 * and   E2 == let P1=R1 in E: S
 *)
(* FIXME: Bug:
 * {let {x} = c1 in let {y} = c1 in c2 x y} should be equal to
 * {let {x} = c1 in let {y} = c1 in c2 y x} *)
and convExpObj1 (E1, E2) = case (NfExpObj.prj E1, NfExpObj.prj E2) of
	  (NfLet (P1, (H1, S1), _), NfLet (P2, (H2, S2), E2')) =>
		if ((convHead (H1, H2); convSpine (S1, S2); true) handle ExnConv _ => false) then E2'
		else
			let val s1 = Subst.shift (nbinds P1)
			in NfLet' (P2,
				(Subst.shiftHead (H2, nbinds P1), NfSClos (S2, s1)),
				NfEClos (convExpObj1 (NfEClos (E1, Subst.shift (nbinds P2)), E2'),
					Subst.switchSub (nbinds P1, nbinds P2)))
			end
	| _ => raise ExnConv "Convertibility failed"

end
