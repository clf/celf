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

structure Syntax :> SYNTAX =
struct

structure Syn2 =
struct
structure Syn1 =
struct

open VRef

(*type 'a h = 'a HashCons.hash_consed*)

datatype kind = FixKind of kind kindF | KClos of kind * subst
and asyncType = FixAsyncType of asyncType asyncTypeF | TClos of asyncType * subst
	| TLogicVar of typeLogicVar | Apx of apxAsyncType
and typeSpine = FixTypeSpine of typeSpine typeSpineF | TSClos of typeSpine * subst
and syncType = FixSyncType of syncType syncTypeF | STClos of syncType * subst
	| ApxS of apxSyncType

and obj = FixObj of obj objF | Clos of obj * subst | EtaTag of obj * int | IntRedex of obj * spine
and spine = FixSpine of spine spineF | SClos of spine * subst
and expObj = FixExpObj of expObj expObjF | EClos of expObj * subst
and monadObj = FixMonadObj of monadObj monadObjF | MClos of monadObj * subst
and pattern = FixPattern of pattern patternF * int | PClos of pattern * subst

and subst = Dot of subObj * subst | Shift of int
and subObj = Ob of obj | Idx of int | Undef

and constr = Solved | Eqn of obj * obj
and head = Const of string
	| Var of int
	| UCVar of string
	| LogicVar of {
		X     : obj option vref,
		ty    : asyncType,
		s     : subst,
		ctx   : asyncType Context.context option ref,
		cnstr : constr vref list vref,
		tag   : word }


and ('aTy, 'ki) kindFF = Type
	| KPi of string option * 'aTy * 'ki
and ('tyS, 'sTy, 'aTy) asyncTypeFF = Lolli of 'aTy * 'aTy
	| TPi of string option * 'aTy * 'aTy
	| AddProd of 'aTy * 'aTy
	| Top
	| TMonad of 'sTy
	| TAtomic of string * 'tyS
	| TAbbrev of string * 'aTy
and ('o, 'tyS) typeSpineFF = TNil
	| TApp of 'o * 'tyS
and ('aTy, 'sTy) syncTypeFF = TTensor of 'sTy * 'sTy
	| TOne
	| Exists of string option * 'aTy * 'sTy
	| Async of 'aTy
and ('aTy, 'sp, 'e, 'o) objFF = LinLam of string * 'o
	| Lam of string * 'o
	| AddPair of 'o * 'o
	| Unit
	| Monad of 'e
	| Atomic of head * 'sp
	| Redex of 'o * apxAsyncType * 'sp
	| Constraint of 'o * 'aTy
and ('sp, 'e, 'o) nfObjFF = NfLinLam of string * 'o
	| NfLam of string * 'o
	| NfAddPair of 'o * 'o
	| NfUnit
	| NfMonad of 'e
	| NfAtomic of head * 'sp
and ('o, 'sp) spineFF = Nil
	| App of 'o * 'sp
	| LinApp of 'o * 'sp
	| ProjLeft of 'sp
	| ProjRight of 'sp
and ('o, 'm, 'p, 'e) expObjFF = Let of 'p * 'o * 'e
	| Mon of 'm
and ('o, 'm) monadObjFF = Tensor of 'm * 'm
	| One
	| DepPair of 'o * 'm
	| Norm of 'o
and ('aTy, 'p) patternFF = PTensor of 'p * 'p
	| POne
	| PDepPair of string * 'aTy * 'p
	| PVar of string * 'aTy

(*and tVarCell = SOM of asyncType | NON of typeLogicVar list ref*)

withtype 'ki kindF = (asyncType, 'ki) kindFF
and 'aTy asyncTypeF = (typeSpine, syncType, 'aTy) asyncTypeFF
and 'tyS typeSpineF = (obj, 'tyS) typeSpineFF
and 'sTy syncTypeF = (asyncType, 'sTy) syncTypeFF
and 'o objF = (asyncType, spine, expObj, 'o) objFF
and 'sp spineF = (obj, 'sp) spineFF
and 'e expObjF = (obj, monadObj, pattern, 'e) expObjFF
and 'm monadObjF = (obj, 'm) monadObjFF
and 'p patternF = (asyncType, 'p) patternFF

and apxKind = kind
and apxAsyncType = asyncType
and apxSyncType = syncType

(* An uninstantiated typeLogicVar t is t=ref (NON L) where L is a list of t and its copies *)
(*and typeLogicVar = tVarCell ref*)
and typeLogicVar = (*apx*)asyncType option ref * word

(*type implicits = (string * asyncType) list*)
datatype typeOrKind = Ty of asyncType | Ki of kind
datatype decl = ConstDecl of string * int * typeOrKind
	| TypeAbbrev of string * asyncType
	| ObjAbbrev of string * asyncType * obj
	| Query of int * int * int * asyncType

type nfKind = kind
type nfAsyncType = asyncType
type nfTypeSpine = typeSpine
type nfSyncType = syncType
type nfObj = obj
type nfSpine = spine
type nfExpObj = expObj
type nfMonadObj = monadObj
type nfPattern = pattern
type nfHead = head

type 'ki nfKindF = (nfAsyncType, 'ki) kindFF
type 'aTy nfAsyncTypeF = (nfTypeSpine, nfSyncType, 'aTy) asyncTypeFF
type 'tyS nfTypeSpineF = (nfObj, 'tyS) typeSpineFF
type 'sTy nfSyncTypeF = (nfAsyncType, 'sTy) syncTypeFF
type 'o nfObjF = (nfSpine, nfExpObj, 'o) nfObjFF
type 'sp nfSpineF = (nfObj, 'sp) spineFF
type 'e nfExpObjF = (nfHead * apxAsyncType * nfSpine, nfMonadObj, nfPattern, 'e) expObjFF
type 'm nfMonadObjF = (nfObj, 'm) monadObjFF
type 'p nfPatternF = (nfAsyncType, 'p) patternFF

datatype ('aTy, 'ki) apxKindFF = ApxType
	| ApxKPi of 'aTy * 'ki
datatype ('sTy, 'aTy) apxAsyncTypeFF = ApxLolli of 'aTy * 'aTy
	| ApxTPi of 'aTy * 'aTy
	| ApxAddProd of 'aTy * 'aTy
	| ApxTop
	| ApxTMonad of 'sTy
	| ApxTAtomic of string
	| ApxTAbbrev of string * asyncType
	| ApxTLogicVar of typeLogicVar
datatype ('aTy, 'sTy) apxSyncTypeFF = ApxTTensor of 'sTy * 'sTy
	| ApxTOne
	| ApxExists of 'aTy * 'sTy
	| ApxAsync of 'aTy
type 'ki apxKindF = (apxAsyncType, 'ki) apxKindFF
type 'aTy apxAsyncTypeF = (apxSyncType, 'aTy) apxAsyncTypeFF
type 'sTy apxSyncTypeF = (apxAsyncType, 'sTy) apxSyncTypeFF

val redex = IntRedex

fun nbinds (FixPattern (_, n)) = n
  | nbinds (PClos (p, _)) = nbinds p
val nfnbinds = nbinds

infix with'ty with's
fun {X, ty=_, s, ctx, cnstr, tag} with'ty ty' = {X=X, ty=ty', s=s, ctx=ctx, cnstr=cnstr, tag=tag}
fun {X, ty, s=_, ctx, cnstr, tag} with's s' = {X=X, ty=ty, s=s', ctx=ctx, cnstr=cnstr, tag=tag}

end (* structure Syn1 *)
open Syn1

(*
structure SS =
struct
datatype 'a simpleStream = Nil | Cons of 'a * (unit -> 'a simpleStream)
fun ThCons (a, s) = fn () => Cons (a, s)
fun ThNil () = Nil
fun eq (Nil, Nil) = true
  | eq (Cons (a1, s1), Cons (a2, s2)) = a1=a2 andalso eq (s1 (), s2 ())
  | eq _ = false
fun foldl f e Nil = e
  | foldl f e (Cons (x, s)) = foldl f (f (x, e)) (s ())
end

fun convKi (FixKind K) a         () = SS.Cons (INL 0w1, SS.ThCons (INL $ HashCons.tag K, a))
  | convKi (KClos (K, s)) a      () = SS.Cons (INL 0w2, convKi K (convSub s a))
and convTy (FixAsyncType A) a    () = SS.Cons (INL 0w3, SS.ThCons (INL $ HashCons.tag A, a))
  | convTy (TClos (A, s)) a      () = SS.Cons (INL 0w4, convTy A (convSub s a))
  | convTy (TLogicVar (_, t)) a  () = SS.Cons (INL 0w5, SS.ThCons (INL t, a))
  | convTy (Apx A) a             () = SS.Cons (INL 0w6, convTy A a)
and convTyS (FixTypeSpine S) a   () = SS.Cons (INL 0w7, SS.ThCons (INL $ HashCons.tag S, a))
  | convTyS (TSClos (S, s)) a    () = SS.Cons (INL 0w8, convTyS S (convSub s a))
and convSTy (FixSyncType S) a    () = SS.Cons (INL 0w9, SS.ThCons (INL $ HashCons.tag S, a))
  | convSTy (STClos (S, s)) a    () = SS.Cons (INL 0w10, convSTy S (convSub s a))
  | convSTy (ApxS S) a           () = SS.Cons (INL 0w11, convSTy S a)
and convObj (FixObj N) a         () = SS.Cons (INL 0w12, SS.ThCons (INL $ HashCons.tag N, a))
  | convObj (Clos (N, s)) a      () = SS.Cons (INL 0w13, convObj N (convSub s a))
  | convObj (EtaTag (N, _)) a    () = SS.Cons (INL 0w14, convObj N a)
  | convObj (IntRedex (N, S)) a  () = SS.Cons (INL 0w15, convObj N (convSp S a))
and convSp (FixSpine S) a        () = SS.Cons (INL 0w16, SS.ThCons (INL $ HashCons.tag S, a))
  | convSp (SClos (S, s)) a      () = SS.Cons (INL 0w17, convSp S (convSub s a))
and convExp (FixExpObj E) a      () = SS.Cons (INL 0w18, SS.ThCons (INL $ HashCons.tag E, a))
  | convExp (EClos (E, s)) a     () = SS.Cons (INL 0w19, convExp E (convSub s a))
and convMon (FixMonadObj M) a    () = SS.Cons (INL 0w20, SS.ThCons (INL $ HashCons.tag M, a))
  | convMon (MClos (M, s)) a     () = SS.Cons (INL 0w21, convMon M (convSub s a))
and convPa (FixPattern (P, _)) a () = SS.Cons (INL 0w22, SS.ThCons (INL $ HashCons.tag P, a))
  | convPa (PClos (P, s)) a      () = SS.Cons (INL 0w23, convPa P (convSub s a))

and convSub (Dot (x, s)) a () = SS.Cons (INL 0w24, convSubObj x (convSub s a))
  | convSub (Shift n) a    () = SS.Cons (INL 0w25, SS.ThCons (INL $ Word.fromInt n, a))
and convSubObj (Ob N) a    () = SS.Cons (INL 0w26, convObj N a)
  | convSubObj (Idx n) a   () = SS.Cons (INL 0w27, SS.ThCons (INL $ Word.fromInt n, a))
  | convSubObj Undef a     () = SS.Cons (INL 0w28, a)

fun convHead (Const c) a () = SS.Cons (INL 0w29, SS.ThCons (INR c, a))
  | convHead (Var n) a   () = SS.Cons (INL 0w30, SS.ThCons (INL $ Word.fromInt n, a))
  | convHead (UCVar x) a () = SS.Cons (INL 0w31, SS.ThCons (INR x, a))
  | convHead (LogicVar {tag, s, ty, ...}) a () =
			SS.Cons (INL 0w32, SS.ThCons (INL tag, convSub s (convTy ty a)))

fun convKiF Type                 = SS.Cons (INL 0w33, SS.ThNil)
  | convKiF (KPi (x, A, K))      = SS.Cons (INL 0w34, SS.ThCons (INR $ getOpt (x, " "),
									convTy A (convKi K SS.ThNil)))
fun convTyF (Lolli (A, B))       = SS.Cons (INL 0w35, convTy A (convTy B SS.ThNil))
  | convTyF (TPi (x, A, B))      = SS.Cons (INL 0w36, SS.ThCons (INR $ getOpt (x, " "),
									convTy A (convTy B SS.ThNil)))
  | convTyF (AddProd (A, B))     = SS.Cons (INL 0w37, convTy A (convTy B SS.ThNil))
  | convTyF Top                  = SS.Cons (INL 0w38, SS.ThNil)
  | convTyF (TMonad S)           = SS.Cons (INL 0w39, convSTy S SS.ThNil)
  | convTyF (TAtomic (x, S))     = SS.Cons (INL 0w40, SS.ThCons (INR x, convTyS S SS.ThNil))
  | convTyF (TAbbrev (x, A))     = SS.Cons (INL 0w41, SS.ThCons (INR x, SS.ThNil))
fun convTySF TNil                = SS.Cons (INL 0w42, SS.ThNil)
  | convTySF (TApp (N, S))       = SS.Cons (INL 0w43, convObj N (convTyS S SS.ThNil))
fun convSTyF (TTensor (S1, S2))  = SS.Cons (INL 0w44, convSTy S1 (convSTy S2 SS.ThNil))
  | convSTyF TOne                = SS.Cons (INL 0w45, SS.ThNil)
  | convSTyF (Exists (x, A, S))  = SS.Cons (INL 0w46, SS.ThCons (INR $ getOpt (x, " "),
									convTy A (convSTy S SS.ThNil)))
  | convSTyF (Async A)           = SS.Cons (INL 0w47, convTy A SS.ThNil)
fun convObjF (LinLam (x, N))     = SS.Cons (INL 0w48, SS.ThCons (INR x, convObj N SS.ThNil))
  | convObjF (Lam (x, N))        = SS.Cons (INL 0w49, SS.ThCons (INR x, convObj N SS.ThNil))
  | convObjF (AddPair (N1, N2))  = SS.Cons (INL 0w50, convObj N1 (convObj N2 SS.ThNil))
  | convObjF Unit                = SS.Cons (INL 0w51, SS.ThNil)
  | convObjF (Monad E)           = SS.Cons (INL 0w52, convExp E SS.ThNil)
  | convObjF (Atomic (h, S))     = SS.Cons (INL 0w53, convHead h (convSp S SS.ThNil))
  | convObjF (Redex (N, A, S))   = SS.Cons (INL 0w54, convObj N (convTy A (convSp S SS.ThNil)))
  | convObjF (Constraint (N, A)) = SS.Cons (INL 0w55, convObj N (convTy A SS.ThNil))
fun convSpF Nil                  = SS.Cons (INL 0w56, SS.ThNil)
  | convSpF (App (N, S))         = SS.Cons (INL 0w57, convObj N (convSp S SS.ThNil))
  | convSpF (LinApp (N, S))      = SS.Cons (INL 0w58, convObj N (convSp S SS.ThNil))
  | convSpF (ProjLeft S)         = SS.Cons (INL 0w59, convSp S SS.ThNil)
  | convSpF (ProjRight S)        = SS.Cons (INL 0w60, convSp S SS.ThNil)
fun convExpF (Let (p, N, E))     = SS.Cons (INL 0w61, convPa p (convObj N (convExp E SS.ThNil)))
  | convExpF (Mon M)             = SS.Cons (INL 0w62, convMon M SS.ThNil)
fun convMonF (Tensor (M1, M2))   = SS.Cons (INL 0w63, convMon M1 (convMon M2 SS.ThNil))
  | convMonF One                 = SS.Cons (INL 0w64, SS.ThNil)
  | convMonF (DepPair (N, M))    = SS.Cons (INL 0w65, convObj N (convMon M SS.ThNil))
  | convMonF (Norm N)            = SS.Cons (INL 0w66, convObj N SS.ThNil)
fun convPaF (PTensor (p1, p2))   = SS.Cons (INL 0w67, convPa p1 (convPa p2 SS.ThNil))
  | convPaF POne                 = SS.Cons (INL 0w68, SS.ThNil)
  | convPaF (PDepPair (x, A, p)) = SS.Cons (INL 0w69, SS.ThCons (INR x, convTy A (convPa p SS.ThNil)))
  | convPaF (PVar (x, A))        = SS.Cons (INL 0w70, SS.ThCons (INR x, convTy A SS.ThNil))


fun mkEq conv (x, y) = SS.eq (conv x, conv y)
fun hashF (INL w, h) = Hash.hashWord (w, h)
  | hashF (INR s, h) = Hash.hashStr (s, h)
fun mkHash conv x = Hash.hashFinal (SS.foldl hashF 0w0 (conv x))
fun mkEqAndHash conv = (mkEq conv, mkHash conv)

val hashTables = {
	ki  = HashCons.newTbl (mkEqAndHash convKiF),
	aTy = HashCons.newTbl (mkEqAndHash convTyF),
	tyS = HashCons.newTbl (mkEqAndHash convTySF),
	sTy = HashCons.newTbl (mkEqAndHash convSTyF),
	o   = HashCons.newTbl (mkEqAndHash convObjF),
	sp  = HashCons.newTbl (mkEqAndHash convSpF),
	e   = HashCons.newTbl (mkEqAndHash convExpF),
	m   = HashCons.newTbl (mkEqAndHash convMonF),
	p   = HashCons.newTbl (mkEqAndHash convPaF) }

val FixKind' = FixKind o HashCons.hashcons (#ki hashTables)
val FixAsyncType' = FixAsyncType o HashCons.hashcons (#aTy hashTables)
val FixTypeSpine' = FixTypeSpine o HashCons.hashcons (#tyS hashTables)
val FixSyncType' = FixSyncType o HashCons.hashcons (#sTy hashTables)
val FixObj' = FixObj o HashCons.hashcons (#o hashTables)
val FixSpine' = FixSpine o HashCons.hashcons (#sp hashTables)
val FixExpObj' = FixExpObj o HashCons.hashcons (#e hashTables)
val FixMonadObj' = FixMonadObj o HashCons.hashcons (#m hashTables)
fun FixPattern' (p, n) = FixPattern (HashCons.hashcons (#p hashTables) p, n)
*)

structure Subst =
struct
	structure Subst' = SubstFun (structure Syn = Syn1 datatype subst = datatype subst)
	open Subst'
	open Syn1
	fun dot (EtaTag (_, n), s) = Dot (Idx n, s)
	  | dot (Clos (Clos (N, s'), s''), s) = dot (Clos (N, comp (s', s'')), s)
	  | dot (Clos (EtaTag (_, n), s'), s) = Dot (Clos' (Idx n, s'), s)
	  | dot (ob, s) = Dot (Ob ob, s)

	fun sub ob = dot (ob, id)
end

fun etaShortcut ob = case Subst.sub ob of Dot (Idx n, _) => SOME n | _ => NONE

structure Signatur = SignaturFun (Syn1)

val lVarCnt = ref 0w0
fun nextLVarCnt () = (lVarCnt := (!lVarCnt) + 0w1 ; !lVarCnt)

val tyLVarCnt = ref 0w0
fun nextTyLVarCnt () = (tyLVarCnt := (!tyLVarCnt) + 0w1 ; !tyLVarCnt)

(*fun newTVar () =
	let val l = ref []
		val t = ref (NON l)
		val () = l := [t]
	in TLogicVar t end
fun newApxTVar () = newTVar ()*)
fun newTVar () = TLogicVar (ref NONE, nextTyLVarCnt ())
fun newApxTVar () = TLogicVar (ref NONE, nextTyLVarCnt ())
fun newLVarCtx ctx ty = FixObj (Atomic (LogicVar {X=vref NONE, ty=ty, s=Subst.id, ctx=ref ctx,
											cnstr=vref [], tag=nextLVarCnt ()}, FixSpine Nil))
val newLVar = newLVarCtx NONE


(* structure Kind : TYP2 where type ('a, 't) F = ('a, 't) kindFF
		and type t = kind and type a = asyncType *)
structure Kind =
struct
	type t = kind type a = asyncType
	type ('a, 't) F = ('a, 't) kindFF
	fun inj k = FixKind k
	fun prj (FixKind k) = (*HashCons.nd*) k
	  | prj (KClos (KClos (k, s'), s)) = prj (KClos (k, Subst.comp (s', s)))
	  | prj (KClos (FixKind k, s)) = Subst.subKind ((*HashCons.nd*) k, s)
	fun Fmap (g, f) Type = Type
	  | Fmap (g, f) (KPi (x, A, K)) = KPi (x, g A, f K)
end
(* structure TypeSpine : TYP2 where type ('a, 't) F = ('a, 't) typeSpineFF
		and type t = typeSpine and type a = obj *)
structure TypeSpine =
struct
	type t = typeSpine type a = obj
	type ('a, 't) F = ('a, 't) typeSpineFF
	fun inj a = FixTypeSpine a
	fun prj (FixTypeSpine a) = (*HashCons.nd*) a
	  | prj (TSClos (TSClos (S, s'), s)) = prj (TSClos (S, Subst.comp (s', s)))
	  | prj (TSClos (FixTypeSpine S, s)) = Subst.subTypeSpine ((*HashCons.nd*) S, s)
	fun Fmap (g, f) TNil = TNil
	  | Fmap (g, f) (TApp (N, S)) = TApp (g N, f S)
	fun newTSpine' ki = case Kind.prj ki of
		  Type => inj TNil
		| KPi (_, A, K) => inj (TApp (newLVar (Apx A), newTSpine' K))
(*		| KPi (_, A, K) => let val N = newLVar A
			in inj (TApp (N, newTSpine' (KClos (K, Subst.sub N)))) end*)
	val newTSpine = newTSpine' o Signatur.sigLookupKind
end
(* structure AsyncType : TYP4 where type ('a, 'b, 't) F = ('a, 'b, 't) asyncTypeFF
		and type t = asyncType and type a = typeSpine and type b = syncType *)
structure AsyncType =
struct
	type t = asyncType type a = typeSpine type b = syncType
	type ('a, 'b, 't) F = ('a, 'b, 't) asyncTypeFF
	fun inj a = FixAsyncType a
	fun Fmap' _ (g, f) (Lolli (A, B)) = Lolli (f A, f B)
	  | Fmap' h (g, f) (TPi (x, A, B)) = TPi (h x, f A, f B)
	  | Fmap' _ (g, f) (AddProd (A, B)) = AddProd (f A, f B)
	  | Fmap' _ (g, f) Top = Top
	  | Fmap' _ ((g1, g2), f) (TMonad S) = TMonad (g2 S)
	  | Fmap' _ ((g1, g2), f) (TAtomic (a, ts)) = TAtomic (a, g1 a ts)
	  | Fmap' _ (g, f) (TAbbrev (a, A)) = TAbbrev (a, f A)
	fun Fmap ((g1, g2), f) a = Fmap' (fn x => x) ((fn _ => g1, g2), f) a 
	fun prjApx (TLogicVar (ref NONE, _)) = raise Fail "Ambiguous typing\n"
	  | prjApx (TLogicVar (ref (SOME a), _)) = prjApx a
	  | prjApx (TClos (a, _)) = prjApx a
	  | prjApx (Apx a) = prjApx a
	  | prjApx (FixAsyncType A) = Fmap' (fn _ => SOME "")
				((fn a => fn _ => TypeSpine.newTSpine a, ApxS), Apx) ((*HashCons.nd*) A)
	fun prj (FixAsyncType a) = (*HashCons.nd*) a
	  | prj (TClos (TClos (a, s'), s)) = prj (TClos (a, Subst.comp (s', s)))
	  | prj (TClos (FixAsyncType a, s)) = Subst.subType ((*HashCons.nd*) a, s)
	  | prj (TClos (TLogicVar (ref NONE, _), _)) = raise Fail "Ambiguous typing\n"
	  | prj (TClos (TLogicVar (ref (SOME a), _), s)) = Subst.subType (prjApx a, s)
	  | prj (TClos (Apx a, s)) = Subst.subType (prjApx a, s)
	  | prj (TLogicVar (ref NONE, _)) = raise Fail "Ambiguous typing\n"
	  | prj (TLogicVar (ref (SOME a), _)) = prjApx a
	  | prj (Apx a) = prjApx a
end
(* structure SyncType : TYP2 where type ('a, 't) F = ('a, 't) syncTypeFF
		and type t = syncType and type a = asyncType *)
structure SyncType =
struct
	type t = syncType type a = asyncType
	type ('a, 't) F = ('a, 't) syncTypeFF
	fun Fmap' _ (g, f) (TTensor (S1, S2)) = TTensor (f S1, f S2)
	  | Fmap' _ (g, f) TOne = TOne
	  | Fmap' h (g, f) (Exists (x, A, S)) = Exists (h x, g A, f S)
	  | Fmap' _ (g, f) (Async A) = Async (g A)
	fun Fmap gf a = Fmap' (fn x => x) gf a
	fun inj a = FixSyncType a
	fun prjApx (FixSyncType S) = Fmap' (fn _ => SOME "") (Apx, ApxS) ((*HashCons.nd*) S)
	  | prjApx (STClos (S, _)) = prjApx S
	  | prjApx (ApxS S) = prjApx S
	fun prj (FixSyncType a) = (*HashCons.nd*) a
	  | prj (STClos (STClos (S, s'), s)) = prj (STClos (S, Subst.comp (s', s)))
	  | prj (STClos (FixSyncType S, s)) = Subst.subSyncType ((*HashCons.nd*) S, s)
	  | prj (STClos (ApxS S, s)) = Subst.subSyncType (prjApx S, s)
	  | prj (ApxS S) = prjApx S
end

(* structure Spine : TYP2 where type ('a, 't) F = ('a, 't) spineFF
		and type t = spine and type a = obj *)
structure Spine =
struct
	type t = spine type a = obj
	type ('a, 't) F = ('a, 't) spineFF
	fun inj a = FixSpine a
	fun prj (FixSpine a) = (*HashCons.nd*) a
	  | prj (SClos (SClos (S, s'), s)) = prj (SClos (S, Subst.comp (s', s)))
	  | prj (SClos (FixSpine S, s)) = Subst.subSpine ((*HashCons.nd*) S, s)
	fun Fmap (g, f) Nil = Nil
	  | Fmap (g, f) (App (N, S)) = App (g N, f S)
	  | Fmap (g, f) (LinApp (N, S)) = LinApp (g N, f S)
	  | Fmap (g, f) (ProjLeft S) = ProjLeft (f S)
	  | Fmap (g, f) (ProjRight S) = ProjRight (f S)
	fun appendSpine (S1', S2) = case prj S1' of
		  Nil => S2
		| LinApp (N, S1) => inj (LinApp (N, appendSpine (S1, S2)))
		| App (N, S1) => inj (App (N, appendSpine (S1, S2)))
		| ProjLeft S1 => inj (ProjLeft (appendSpine (S1, S2)))
		| ProjRight S1 => inj (ProjRight (appendSpine (S1, S2)))
end
(* structure Obj : TYP4 where type ('a, 'b, 'c, 't) F = ('a, 'b, 'c, 't) objFF
		and type t = obj and type a = asyncType and type b = spine and type c = expObj *)
structure Obj =
struct
	fun tryLVar (a as Atomic (LogicVar {X, s, ...}, S)) =
			Option.map (fn N => (Clos (N, s), S)) (!!X)
	  | tryLVar a = NONE
	type t = obj type a = asyncType type b = spine type c = expObj
	type ('a, 'b, 'c, 't) F = ('a, 'b, 'c, 't) objFF
	fun inj a = FixObj a
	fun prj (FixObj N) = let val N = (*HashCons.nd*) N
			in case tryLVar N of NONE => N | SOME obS => intRedex obS end
	  | prj (Clos (Clos (N, s'), s)) = prj (Clos (N, Subst.comp (s', s)))
	  | prj (Clos (FixObj N, s)) = let val N = (*HashCons.nd*) N
	  		in case tryLVar N of
				  NONE => Subst.subObj intRedex (N, s)
				| SOME (ob, S) => intRedex (Clos (ob, s), SClos (S, s)) end
	  | prj (Clos (EtaTag (N, _), s)) = prj (Clos (N, s))
	  | prj (Clos (IntRedex (N, S), s)) = intRedex (Clos (N, s), SClos (S, s))
	  | prj (EtaTag (N, _)) = prj N
	  | prj (IntRedex (N, S)) = intRedex (N, S)
	and intRedex (ob, sp) = case (prj ob, Spine.prj sp) of
		  (N, Nil) => N
		| (LinLam (_, N1), LinApp (N2, S)) => intRedex (Clos (N1, Subst.sub N2), S)
		| (Lam (_, N1), App (N2, S)) => intRedex (Clos (N1, Subst.sub N2), S)
		| (AddPair (N, _), ProjLeft S) => intRedex (N, S)
		| (AddPair (_, N), ProjRight S) => intRedex (N, S)
		| (Atomic (H, S1), S2) => Atomic (H, Spine.appendSpine (S1, Spine.inj S2))
		| (Redex (N, A, S1), S2) => Redex (N, A, Spine.appendSpine (S1, Spine.inj S2))
		| (Constraint (N, A), S) => intRedex (N, Spine.inj S)
		| _ => raise Fail "Internal error: intRedex\n"
	fun Fmap (g, f) (LinLam (x, N)) = (LinLam (x, f N))
	  | Fmap (g, f) (Lam (x, N)) = (Lam (x, f N))
	  | Fmap (g, f) (AddPair (N1, N2)) = (AddPair (f N1, f N2))
	  | Fmap (g, f) Unit = Unit
	  | Fmap ((g1, g2, g3), f) (Monad E) = Monad (g3 E)
	  | Fmap ((g1, g2, g3), f) (Atomic (h, S)) = Atomic (h, g2 S)
	  | Fmap ((g1, g2, g3), f) (Redex (N, A, S)) = Redex (f N, A, g2 S)
	  | Fmap ((g1, g2, g3), f) (Constraint (N, A)) = Constraint (f N, g1 A)
end
(* structure ExpObj : TYP4 where type ('a, 'b, 'c, 't) F = ('a, 'b, 'c, 't) expObjFF
		and type t = expObj and type a = obj and type b = monadObj and type c = pattern *)
structure ExpObj =
struct
	type t = expObj type a = obj type b = monadObj type c = pattern
	type ('a, 'b, 'c, 't) F = ('a, 'b, 'c, 't) expObjFF
	fun inj a = FixExpObj a
	fun prj (FixExpObj a) = (*HashCons.nd*) a
	  | prj (EClos (EClos (E, s'), s)) = prj (EClos (E, Subst.comp (s', s)))
	  | prj (EClos (FixExpObj E, s)) = Subst.subExpObj ((*HashCons.nd*) E, s)
	fun Fmap ((g1, g2, g3), f) (Let (p, N, E)) = Let (g3 p, g1 N, f E)
	  | Fmap ((g1, g2, g3), f) (Mon M) = Mon (g2 M)
end
(* structure MonadObj : TYP2 where type ('a, 't) F = ('a, 't) monadObjFF
		and type t = monadObj and type a = obj *)
structure MonadObj =
struct
	type t = monadObj type a = obj
	type ('a, 't) F = ('a, 't) monadObjFF
	fun inj a = FixMonadObj a
	fun prj (FixMonadObj a) = (*HashCons.nd*) a
	  | prj (MClos (MClos (M, s'), s)) = prj (MClos (M, Subst.comp (s', s)))
	  | prj (MClos (FixMonadObj M, s)) = Subst.subMonadObj ((*HashCons.nd*) M, s)
	fun Fmap (g, f) (Tensor (M1, M2)) = Tensor (f M1, f M2)
	  | Fmap (g, f) One = One
	  | Fmap (g, f) (DepPair (N, M)) = DepPair (g N, f M)
	  | Fmap (g, f) (Norm N) = Norm (g N)
end
(* structure Pattern : TYP2 where type ('a, 't) F = ('a, 't) patternFF
		and type t = pattern and type a = asyncType *)
structure Pattern =
struct
	type t = pattern type a = asyncType
	type ('a, 't) F = ('a, 't) patternFF
	fun pbinds (PTensor (p1, p2)) = nbinds p1 + nbinds p2
	  | pbinds POne = 0
	  | pbinds (PDepPair (_, _, p)) = 1 + nbinds p
	  | pbinds (PVar _) = 1
	fun inj a = FixPattern (a, pbinds a)
	fun prj (FixPattern (a, _)) = (*HashCons.nd*) a
	  | prj (PClos (PClos (p, s'), s)) = prj (PClos (p, Subst.comp (s', s)))
	  | prj (PClos (FixPattern (p, _), s)) = Subst.subPattern ((*HashCons.nd*) p, s)
	fun Fmap (g, f) (PTensor (p1, p2)) = PTensor (f p1, f p2)
	  | Fmap (g, f) POne = POne
	  | Fmap (g, f) (PDepPair (x, A, p)) = PDepPair (x, g A, f p)
	  | Fmap (g, f) (PVar (x, A)) = PVar (x, g A)
end

(*
val consistencyTable = ref (Binarymap.mkDict Int.compare)
fun consistencyCheck (LogicVar {X, tag, cnstr, ...}) =
		(case Binarymap.peek (!consistencyTable, tag) of
			  NONE =>
				( Binarymap.app
					(fn (_, (r, cs)) => if eq (r, X) orelse eq (cs, cnstr) then
						( print ("Consistency check failed on new $"^Int.toString tag)
						; raise Fail "Consistency new" ) else ())
				; consistencyTable := Binarymap.insert (!consistencyTable, tag, (X, cnstr)) )
			| SOME (r, cs) =>
				if eq (r, X) andalso eq (cs, cnstr) then ()
				else
					( print ("Consistency check failed on $"^Int.toString tag)
					; raise Fail "Consistency" ))
  | consistencyCheck _ = ()
fun Atomic' hAS = (consistencyCheck (#1 hAS); Obj.inj (Atomic hAS))
*)

val Type' = Kind.inj Type
val KPi' = Kind.inj o KPi
val Lolli' = AsyncType.inj o Lolli
val TPi' = AsyncType.inj o TPi
val AddProd' = AsyncType.inj o AddProd
val Top' = AsyncType.inj Top
val TMonad' = AsyncType.inj o TMonad
val TAtomic' = AsyncType.inj o TAtomic
val TAbbrev' = AsyncType.inj o TAbbrev
val TNil' = TypeSpine.inj TNil
val TApp' = TypeSpine.inj o TApp
val TTensor' = SyncType.inj o TTensor
val TOne' = SyncType.inj TOne
val Exists' = SyncType.inj o Exists
val Async' = SyncType.inj o Async
val LinLam' = Obj.inj o LinLam
val Lam' = Obj.inj o Lam
val AddPair' = Obj.inj o AddPair
val Unit' = Obj.inj Unit
val Monad' = Obj.inj o Monad
val Atomic' = Obj.inj o Atomic
val Redex' = Obj.inj o Redex
val Constraint' = Obj.inj o Constraint
val Nil' = Spine.inj Nil
val App' = Spine.inj o App
val LinApp' = Spine.inj o LinApp
val ProjLeft' = Spine.inj o ProjLeft
val ProjRight' = Spine.inj o ProjRight
val Let' = ExpObj.inj o Let
val Mon' = ExpObj.inj o Mon
val Tensor' = MonadObj.inj o Tensor
val One' = MonadObj.inj One
val DepPair' = MonadObj.inj o DepPair
val Norm' = MonadObj.inj o Norm
val PTensor' = Pattern.inj o PTensor
val POne' = Pattern.inj POne
val PDepPair' = Pattern.inj o PDepPair
val PVar' = Pattern.inj o PVar

val appendSpine = Spine.appendSpine

end (* structure Syn2 *)
open Syn2


structure Whnf = WhnfFun (Syn2)

(* structure NfKind : TYP2 where type ('a, 't) F = ('a, 't) kindFF
		and type t = nfKind and type a = nfAsyncType *)
(* structure NfAsyncType : TYP4 where type ('a, 'b, 't) F = ('a, 'b, 't) asyncTypeFF
		and type t = nfAsyncType and type a = nfTypeSpine and type b = nfSyncType *)
(* structure NfTypeSpine : TYP2 where type ('a, 't) F = ('a, 't) typeSpineFF
		and type t = nfTypeSpine and type a = nfObj *)
(* structure NfSyncType : TYP2 where type ('a, 't) F = ('a, 't) syncTypeFF
		and type t = nfSyncType and type a = nfAsyncType *)
structure NfKind = Kind
structure NfAsyncType = AsyncType
structure NfTypeSpine = TypeSpine
structure NfSyncType = SyncType

(* structure NfObj : TYP3 where type ('a, 'b, 't) F = ('a, 'b, 't) nfObjFF
		and type t = nfObj and type a = nfSpine and type b = nfExpObj *)
structure NfObj =
struct
	type t = nfObj type a = nfSpine type b = nfExpObj
	type ('a, 'b, 't) F = ('a, 'b, 't) nfObjFF
	fun inj (NfLinLam xN) = FixObj (LinLam xN)
	  | inj (NfLam xN) = FixObj (Lam xN)
	  | inj (NfAddPair N1N2) = FixObj (AddPair N1N2)
	  | inj NfUnit = FixObj Unit
	  | inj (NfMonad E) = FixObj (Monad E)
	  | inj (NfAtomic at) = FixObj (Atomic at)
	val prj = Whnf.whnfObj
	fun Fmap (g, f) (NfLinLam (x, N)) = NfLinLam (x, f N)
	  | Fmap (g, f) (NfLam (x, N)) = NfLam (x, f N)
	  | Fmap (g, f) (NfAddPair (N1, N2)) = NfAddPair (f N1, f N2)
	  | Fmap (g, f) NfUnit = NfUnit
	  | Fmap ((g1, g2), f) (NfMonad E) = NfMonad (g2 E)
	  | Fmap ((g1, g2), f) (NfAtomic (h, S)) = NfAtomic (h, g1 S)
end
(* structure NfExpObj : TYP4 where type ('a, 'b, 'c, 't) F = (nfHead * apxAsyncType * 'a, 'b, 'c, 't) expObjFF
		and type t = nfExpObj and type a = nfSpine and type b = nfMonadObj and type c = nfPattern *)
structure NfExpObj =
struct
	type t = nfExpObj type a = nfSpine type b = nfMonadObj type c = nfPattern
	type ('a, 'b, 'c, 't) F = (nfHead * 'a, 'b, 'c, 't) expObjFF
	fun inj (Let (p, hS, E)) = FixExpObj (Let (p, FixObj (Atomic hS), E))
	  | inj (Mon M) = FixExpObj (Mon M)
	val prj = Whnf.whnfExp
	fun Fmap ((g1, g2, g3), f) (Let (p, (h, S), E)) = Let (g3 p, (h, g1 S), f E)
	  | Fmap ((g1, g2, g3), f) (Mon M) = Mon (g2 M)
end
(* structure NfSpine : TYP2 where type ('a, 't) F = ('a, 't) spineFF
		and type t = nfSpine and type a = nfObj *)
(* structure NfMonadObj : TYP2 where type ('a, 't) F = ('a, 't) monadObjFF
		and type t = nfMonadObj and type a = nfObj *)
(* structure NfPattern : TYP2 where type ('a, 't) F = ('a, 't) patternFF
		and type t = nfPattern and type a = nfAsyncType *)
structure NfSpine = Spine
structure NfMonadObj = MonadObj
structure NfPattern = Pattern

val NfKClos = KClos
val NfTClos = TClos
val NfTSClos = TSClos
val NfSTClos = STClos
val NfClos = Clos
val NfSClos = SClos
val NfEClos = EClos
val NfMClos = MClos
val NfPClos = PClos



(* structure ApxKind : TYP2 where type ('a, 't) F = ('a, 't) apxKindFF
		and type t = apxKind and type a = apxAsyncType *)
structure ApxKind =
struct
	type t = apxKind type a = apxAsyncType
	type ('a, 't) F = ('a, 't) apxKindFF
	fun inj ApxType = Kind.inj Type
	  | inj (ApxKPi (A, K)) = Kind.inj (KPi (SOME "", A, K))
	fun prj (KClos (K, _)) = prj K
	  | prj k = case Kind.prj k of
		  Type => ApxType
		| KPi (_, A, K) => ApxKPi (A, K)
	fun Fmap (g, f) ApxType = ApxType
	  | Fmap (g, f) (ApxKPi (A, K)) = ApxKPi (g A, f K)
end
(* structure ApxAsyncType : TYP2 where type ('a, 't) F = ('a, 't) apxAsyncTypeFF
		and type t = apxAsyncType and type a = apxSyncType *)
structure ApxAsyncType =
struct
	type t = apxAsyncType type a = syncType
	type ('a, 't) F = ('a, 't) apxAsyncTypeFF
	fun inj (ApxLolli (A, B)) = AsyncType.inj (Lolli (A, B))
	  | inj (ApxTPi (A, B)) = AsyncType.inj (TPi (SOME "", A, B))
	  | inj (ApxAddProd (A, B)) = AsyncType.inj (AddProd (A, B))
	  | inj ApxTop = AsyncType.inj Top
	  | inj (ApxTMonad S) = AsyncType.inj (TMonad S)
	  | inj (ApxTAtomic a) = AsyncType.inj (TAtomic (a, TypeSpine.inj TNil)) (*Signatur.sigNewTAtomic a*)
	  | inj (ApxTAbbrev aA) = AsyncType.inj (TAbbrev aA)
	  | inj (ApxTLogicVar X) = TLogicVar X
	fun prj (TLogicVar (ref (SOME A), _)) = prj A
	  | prj (TLogicVar (X as (ref NONE, _))) = ApxTLogicVar X
	  | prj (TClos (A, _)) = prj A
	  | prj (Apx A) = prj A
	  | prj a = case AsyncType.prj a of
		  Lolli (A, B) => ApxLolli (A, B)
		| TPi (_, A, B) => ApxTPi (A, B)
		| AddProd (A, B) => ApxAddProd (A, B)
		| Top => ApxTop
		| TMonad S => ApxTMonad S
		| TAtomic (a, _) => ApxTAtomic a
		| TAbbrev (a, A) => ApxTAbbrev (a, A)
	fun Fmap (g, f) (ApxLolli (A, B)) = ApxLolli (f A, f B)
	  | Fmap (g, f) (ApxTPi (A, B)) = ApxTPi (f A, f B)
	  | Fmap (g, f) (ApxAddProd (A, B)) = ApxAddProd (f A, f B)
	  | Fmap (g, f) ApxTop = ApxTop
	  | Fmap (g, f) (ApxTMonad S) = ApxTMonad (g S)
	  | Fmap (g, f) (ApxTAtomic a) = ApxTAtomic a
	  | Fmap (g, f) (ApxTAbbrev aA) = ApxTAbbrev aA
	  | Fmap (g, f) (ApxTLogicVar X) = ApxTLogicVar X
end
(* structure ApxSyncType : TYP2 where type ('a, 't) F = ('a, 't) apxSyncTypeFF
		and type t = apxSyncType and type a = apxAsyncType *)
structure ApxSyncType =
struct
	type t = apxSyncType type a = apxAsyncType
	type ('a, 't) F = ('a, 't) apxSyncTypeFF
	fun inj (ApxTTensor (S1, S2)) = SyncType.inj (TTensor (S1, S2))
	  | inj ApxTOne = SyncType.inj TOne
	  | inj (ApxExists (A, S)) = SyncType.inj (Exists (SOME "", A, S))
	  | inj (ApxAsync A) = SyncType.inj (Async A)
	fun prj (STClos (S, _)) = prj S
	  | prj (ApxS S) = prj S
	  | prj s = case SyncType.prj s of
		  TTensor (S1, S2) => ApxTTensor (S1, S2)
		| TOne => ApxTOne
		| Exists (_, A, S) => ApxExists (A, S)
		| Async A => ApxAsync A
	fun Fmap (g, f) (ApxTTensor (S1, S2)) = ApxTTensor (f S1, f S2)
	  | Fmap (g, f) ApxTOne = ApxTOne
	  | Fmap (g, f) (ApxExists (A, S)) = ApxExists (g A, f S)
	  | Fmap (g, f) (ApxAsync A) = ApxAsync (g A)
end

val ApxType' = ApxKind.inj ApxType
val ApxKPi' = ApxKind.inj o ApxKPi
val ApxLolli' = ApxAsyncType.inj o ApxLolli
val ApxTPi' = ApxAsyncType.inj o ApxTPi
val ApxAddProd' = ApxAsyncType.inj o ApxAddProd
val ApxTop' = ApxAsyncType.inj ApxTop
val ApxTMonad' = ApxAsyncType.inj o ApxTMonad
val ApxTAtomic' = ApxAsyncType.inj o ApxTAtomic
val ApxTAbbrev' = ApxAsyncType.inj o ApxTAbbrev
val ApxTLogicVar' = ApxAsyncType.inj o ApxTLogicVar
val ApxTTensor' = ApxSyncType.inj o ApxTTensor
val ApxTOne' = ApxSyncType.inj ApxTOne
val ApxExists' = ApxSyncType.inj o ApxExists
val ApxAsync' = ApxSyncType.inj o ApxAsync

structure ApxKindRec = Rec2 (structure T = ApxKind)
structure ApxAsyncTypeRec = Rec2 (structure T = ApxAsyncType)
structure ApxSyncTypeRec = Rec2 (structure T = ApxSyncType)

(*fun copyLVar (ref (NON L)) =
		let val t = ref (NON L)
			val () = L := t :: !L
		in t end
  | copyLVar _ = raise Fail "Internal error: copyLVar called on instantiated LVars"*)
(*fun eqLVar (ref (NON L1), ref (NON L2)) = L1 = L2*)
fun eqLVar ((X1 as ref NONE, _), (X2 as ref NONE, _)) = X1 = X2
  | eqLVar _ = raise Fail "Internal error: eqLVar called on instantiated LVars"

type ('ki, 'aTy, 'sTy) apxFoldFuns = {
	fki  : ('aTy, 'ki) apxKindFF -> 'ki,
	faTy : ('sTy, 'aTy) apxAsyncTypeFF -> 'aTy,
	fsTy : ('aTy, 'sTy) apxSyncTypeFF -> 'sTy }

fun foldApxKind (fs : ('ki, 'aTy, 'sTy) apxFoldFuns) x =
			ApxKindRec.fold (foldApxType fs) (#fki fs) x
and foldApxType fs x = ApxAsyncTypeRec.fold (foldApxSyncType fs) (#faTy fs) x
and foldApxSyncType fs x = ApxSyncTypeRec.fold (foldApxType fs) (#fsTy fs) x

(*fun cpLVar (ApxTLogicVar X) = ApxTLogicVar (copyLVar X)
  | cpLVar A = A
val apxCopyFfs = {fki = ApxKind.inj, faTy = ApxAsyncType.inj o cpLVar, fsTy = ApxSyncType.inj}*)

(* updLVar : typeLogicVar * apxAsyncType -> unit *)
fun updLVar ((ref (SOME _), _), _) = raise Fail "typeLogicVar already updated\n"
  | updLVar ((X as ref NONE, _), A) = X := SOME A (*(foldApxType apxCopyFfs A)*)
  (*| updLVar (ref (NON L), A) = app (fn X => X := SOM (foldApxType apxCopyFfs A)) (!L)*)

(* isUnknown : asyncType -> bool *)
fun isUnknown (TClos (A, _)) = isUnknown A
  | isUnknown (FixAsyncType _) = false
  | isUnknown (TLogicVar (ref (SOME A), _)) = isUnknown A
  | isUnknown (TLogicVar (ref NONE, _)) = true
  | isUnknown (Apx A) = isUnknown A

fun kindToApx x = x
fun asyncTypeToApx x = x
fun syncTypeToApx x = x

(*val asyncTypeFromApx = foldApxType apxCopyFfs
val syncTypeFromApx = foldApxSyncType apxCopyFfs
val kindFromApx = foldApxKind apxCopyFfs*)
fun injectApxType x = Apx x
fun injectApxSyncType x = ApxS x
(*fun asyncTypeFromApx x = Apx x
fun syncTypeFromApx x = ApxS x*)
(*fun kindFromApx x = ApxK x*)
fun unsafeCast x = x

fun normalizeKind x = x
fun normalizeType x = x
fun normalizeObj x = x
fun normalizeExpObj x = x

fun unnormalizeKind x = x
fun unnormalizeType x = x
fun unnormalizeObj x = x
fun unnormalizeExpObj x = x
fun unnormalizePattern x = x

end
