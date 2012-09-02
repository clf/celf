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

signature TLU_Match = TOP_LEVEL_UTIL
structure Match :> MATCH =
struct

open VRef infix ::=
open Syntax infix with's
open Context
open PatternBind

val outputMatch = ref false

exception ExnMatch of string

val numInst = ref 0

(* instantiate : nfObj option vref * nfObj * constr vref list vref * word -> unit *)
fun instantiate (r, rInst, l : int (* word *)) =
    if isSome (!! r) then raise Fail "Internal error: double instantiation" else
    ( r ::= SOME rInst
    ; numInst := !numInst + 1
    ; if !outputMatch then
        print ("Instantiating ("^Int.toString (!numInst)^") $"^(Int.toString (* Word.toString *) l)^" = "
               ^(PrettyPrint.printObj $ unnormalizeObj rInst)^"\n")
      else () )

(* lowerLVar : nfAsyncType * nfSpine * subst * context -> nfObj * nfObj nfObjF *)
(* Invariant:
 * lowerLVar (ty, sp, s, G) = (rInst, Y)
 * G |- rInst : ty
 * G1' |- s : G
 * G2' |- sp : ty[s] > a
 * G1'+G2' |- Y = rInst[s] sp : a
 *)
fun lowerLVar (ty, sp, s, ctx) =
    case (Util.nfTypePrjAbbrev ty, NfSpine.prj sp) of
      (TLPi (p, A, B), LApp (M, S)) =>
      let val p' = Util.patternT2O p
          val (rInst, Y) = lowerLVar (B, S, Subst.dotMonad (M, s), opatBindNf (p', A) ctx)
      in (NfLLam' (p', rInst), Y) end
    | (AddProd (A, B), ProjLeft S) =>
      let val (rInst, Y) = lowerLVar (A, S, s, ctx)
      in (NfAddPair' (rInst, newNfLVarCtx (SOME ctx) B), Y) end
    | (AddProd (A, B), ProjRight S) =>
      let val (rInst, Y) = lowerLVar (B, S, s, ctx)
      in (NfAddPair' (newNfLVarCtx (SOME ctx) A, rInst), Y) end
    | (TAtomic _, Nil) =>
      let val X = newNfLVarCtx (SOME ctx) ty
      in (X, NfObj.prj $ NfClos (X, s)) end
    | (TMonad _, Nil) =>
      let val X = newNfLVarCtx (SOME ctx) ty
      in (X, NfObj.prj $ NfClos (X, s)) end
    | _ => raise Fail "Internal error: lowerLVar"

fun invAtomic (NfAtomic a) = a
  | invAtomic _ = raise Fail "Internal error: invAtomic"

(* lowerAtomic : nfHead * nfSpine -> nfHead * nfSpine *)
fun lowerAtomic (N as (LogicVar {X, ty, s, ctx=ref ctx, cnstr=cs, tag}, S)) =
    (case NfSpine.prj S of
       Nil => N
     | _ =>
       let
         val (rInst, Y) = lowerLVar (ty, S, s, valOf ctx)
       in
         instantiate (X, rInst, tag); invAtomic Y
       end)
  | lowerAtomic hS = hS

fun lowerObj (NfAtomic hS) = NfAtomic (lowerAtomic hS)
  | lowerObj N = N

fun lowerExp (NfLet (p, hS, E)) = NfLet (p, lowerAtomic hS, E)
  | lowerExp E = E

fun isLVar (LogicVar _, _) = true
  | isLVar _ = false

fun invLVar (LogicVar Z, _) = Z
  | invLVar _ = raise Fail "Internal error: invLVar"

fun pat2mon p =
    let
      open NfInj
      fun pat2mon' p n =
          case Pattern.prj p of
            PDepTensor (p1, p2) => DepPair' (pat2mon' p1 (n + nbinds p2), pat2mon' p2 n)
          | POne => One'
          | PDown _ => Down' (NfAtomic' (Var (LIN, n), Nil'))
          | PAffi _ => Affi' (NfAtomic' (Var (AFF, n), Nil'))
          | PBang _ => Bang' (NfAtomic' (Var (INT, n), Nil'))
    in
      pat2mon' p 1
    end

(* matchObj (ob1, ob2)
 * matches pattern object ob1 against ground object ob2
 * Raises ExnMatch if matching fails; returns () if matching succeeds *)
fun matchObj (obPat', obGnd') =
    let
      val obPat = lowerObj (NfObj.prj (obPat'))
      val obGnd = NfObj.prj (obGnd')
      open NfInj
      fun invLam p hS = nfredex (NfClos (NfAtomic' hS, Subst.shift $ nbinds p),
                                 LApp' (pat2mon p, Nil'))
      fun invPair p hS = nfredex (NfAtomic' hS, p Nil')
    in
      case (obPat, obGnd) of
        (NfLLam (_, N1), NfLLam (_, N2)) => matchObj (N1, N2)
      | (NfLLam (p, N2), NfAtomic hS1) => raise ExnMatch "matchObj NfLLam-NfAtomic"
      | (NfAtomic hS1, NfLLam (p, N2)) => matchObj (invLam p hS1, N2)
      | (NfAddPair (L1, N1), NfAddPair (L2, N2)) =>
        ( matchObj (L1, L2)
        ; matchObj (N1, N2) )
      | (NfAtomic hS1, NfAddPair (L2, N2)) =>
        ( matchObj (invPair ProjLeft' hS1, L2)
        ; matchObj (invPair ProjRight' hS1, N2) )
      | (NfAddPair (L1, N1), NfAtomic hS2) => raise ExnMatch "matchObj NfAddPair-NfAtomic"
      | (NfMonad E1, NfMonad E2) => print "Warning: matching on traces is not implemented (Monad-Monad)"
      | (NfAtomic hS, NfMonad E) => print "Warning: matching on traces is not implemented (Atomic-Monad)"
      | (NfMonad E, NfAtomic hS) => print "Warning: matching on traces is not implemented (Monad-Atomic)"
      | (NfAtomic hS1, NfAtomic hS2) => matchHeadSp (hS1, hS2)
      | (N1, N2) => raise Fail "Internal error: matchObj"
    end
and matchHeadSp (hS1 as (h1, S1), hS2 as (h2, S2)) =
    case (h1, h2) of
      (Const c1, Const c2) => if c1 <> c2
                              then raise ExnMatch "matchHeadSp Const-Const"
                              else matchSpine (S1, S2)
    | (UCVar x1, UCVar x2) => if x1 <> x2
                              then raise ExnMatch "matchHeadSp UCVar-UCVar"
                              else matchSpine (S1, S2)
    | (Var n1, Var n2) => if n1 <> n2
                          then raise ExnMatch "matchObj Var-Var"
                          else matchSpine (S1, S2)
    | (LogicVar (X as {X=r, s, tag, ctx, ...}), _) =>
      let
        fun patSub s = Subst.patSub (fn ob => (ob, true)) Eta.etaContract s
        val sinv = case patSub s of
                     NONE => raise Fail "Internal error: not a pattern substitution"
                   | SOME ([], s') => Subst.invert s'
                   | SOME (_, _) => raise Fail "Internal error: linear-changing?"
      in
        instantiate (r, NfClos (NfAtomic' hS2, sinv), tag)
        (* Context is needed for typechecking *)
      ; if not (TypeCheck.isEnabled ()) then ctx := NONE else () (* TODO: check if this is safe *)
      end
    | (_, LogicVar _) => raise Fail "Internal error: ground side contains LVar"
    | _ => raise ExnMatch "matchHeadSp"
and matchSpine (sp1, sp2) =
    case (NfSpine.prj sp1, NfSpine.prj sp2) of
      (Nil, Nil) => ()
    | (LApp (M1, S1), LApp (M2, S2)) => (matchMon (M1, M2); matchSpine (S1, S2))
    | (ProjLeft S1, ProjLeft S2) => matchSpine (S1, S2)
    | (ProjRight S1, ProjRight S2) => matchSpine (S1, S2)
    | (ProjLeft _, ProjRight _) => raise ExnMatch "matchSpine Left-Right"
    | (ProjRight _, ProjLeft _) => raise ExnMatch "matchSpine Right-Left"
    | _ => raise Fail "Internal error: matchSpine"
and matchMon (m1, m2) =
    case (NfMonadObj.prj m1, NfMonadObj.prj m2) of
      (DepPair (M11, M12), DepPair (M21, M22)) =>
      (matchMon (M11, M21); matchMon (M12, M22))
    | (One, One) => ()
    | (Down N1, Down N2) => matchObj (N1, N2)
    | (Affi N1, Affi N2) => matchObj (N1, N2)
    | (Bang N1, Bang N2) => matchObj (N1, N2)
    | (MonUndef, _) => raise Fail "Internal error: matchMon: MonUndef"
    | (_, MonUndef) => raise Fail "Internal error: matchMon: MonUndef"
    | _ => raise Fail "Internal error: matchMon"


fun match (ob1, ob2) sc =
    (matchObj (normalizeObj ob1, normalizeObj ob2); sc () )
    handle ExnMatch _ => ()

fun matchList (obs1, obs2) sc =
    let
      fun matchList' obs1 obs2 sc = List.foldr (fn (ob, r) => fn () => match ob r) sc (ListPair.zip (obs1, obs2))
    in
      matchList' obs1 obs2 sc ()
    end

end
