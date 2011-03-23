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

signature TLU_Syntax = TOP_LEVEL_UTIL
structure Syntax :> SYNTAX =
struct

structure Syn2 =
struct
structure Syn1 =
struct

open VRef

(*type 'a h = 'a HashCons.hash_consed*)

datatype subMode = ID | INT4LIN | INT4AFF | AFF4LIN

datatype ('x, 'ix, 'p) patternF
	= PDepTensor of 'p * 'p
	| POne
	| PDown of 'x
	| PAffi of 'x
	| PBang of 'ix
datatype ('x, 'ix) pattern = FixPattern of ('x, 'ix, ('x, 'ix) pattern) patternF * int
type opattern = (string, string) pattern
type tpattern = (unit, string option) pattern

(* empty types used as phantom type markers on substitutions *)
datatype pat = PAT of pat
datatype pat_ = PAT_ of pat_
datatype gen = GEN of gen

datatype kind = FixKind of kind kindF | KClos of kind * subst
and asyncType = FixAsyncType of asyncType asyncTypeF | TClos of asyncType * subst
	| TLogicVar of typeLogicVar | Apx of apxAsyncType
and typeSpine = FixTypeSpine of typeSpine typeSpineF | TSClos of typeSpine * subst
and syncType = FixSyncType of syncType syncTypeF | STClos of syncType * subst
	| ApxS of apxSyncType

and obj = FixObj of obj objF | Clos of obj * subst | EtaTag of obj * (Context.mode * int)
	| IntRedex of obj * spine
and spine = FixSpine of spine spineF | SClos of spine * subst
and expObj = FixExpObj of expObj expObjF | EClos of expObj * subst
	| IntLetRedex of opattern * obj * expObj
and monadObj = FixMonadObj of monadObj monadObjF | MClos of monadObj * subst

and subst' = Dot of subObj * subst' | Shift of int
and subObj = Ob of Context.mode * nfObj | Idx of subMode * int | Undef

and constr
	= Solved
	| Eqn of nfObj * nfObj * (unit -> string)
	| Exist of nfObj * (unit -> string)
and 'aTy headF = Const of string
	| Var of Context.mode * int
	| UCVar of string
	| LogicVar of {
		X     : nfObj option vref,
		ty    : 'aTy,
		s     : subst,
		ctx   : 'aTy Context.context option ref,
		cnstr : constr vref list vref,
		tag   : word }


and ('aTy, 'ki) kindFF
	= Type
	| KPi of string option * 'aTy * 'ki
and ('tyS, 'sTy, 'aTy) asyncTypeFF
	= TLPi of tpattern * 'sTy * 'aTy
	| AddProd of 'aTy * 'aTy
	| TMonad of 'sTy
	| TAtomic of string * 'tyS
	| TAbbrev of string * 'aTy
and ('o, 'tyS) typeSpineFF
	= TNil
	| TApp of 'o * 'tyS
and ('aTy, 'sTy) syncTypeFF
	= LExists of tpattern * 'sTy * 'sTy
	| TOne
	| TDown of 'aTy
	| TAffi of 'aTy
	| TBang of 'aTy
and ('aTy, 'sp, 'e, 'o) objFF
	= LLam of opattern * 'o
	| AddPair of 'o * 'o
	| Monad of 'e
	| Atomic of head * 'sp
	| Redex of 'o * apxAsyncType * 'sp
	| Constraint of 'o * 'aTy
and ('sp, 'e, 'o) nfObjFF
	= NfLLam of opattern * 'o
	| NfAddPair of 'o * 'o
	| NfMonad of 'e
	| NfAtomic of nfHead * 'sp
and ('m, 'sp) spineFF
	= Nil
	| LApp of 'm * 'sp
	| ProjLeft of 'sp
	| ProjRight of 'sp
and ('o, 'sp, 'm, 'e) expObjFF
	= LetRedex of opattern * apxSyncType * 'o * 'e
	| Let of opattern * (head * 'sp) * 'e
	| Mon of 'm
and ('sp, 'm, 'e) nfExpObjFF
	= NfLet of opattern * (nfHead * 'sp) * 'e
	| NfMon of 'm
and ('o, 'm) monadObjFF
	= DepPair of 'm * 'm
	| One
	| Down of 'o
	| Affi of 'o
	| Bang of 'o
	| MonUndef

withtype 'ki kindF = (asyncType, 'ki) kindFF
and 'aTy asyncTypeF = (typeSpine, syncType, 'aTy) asyncTypeFF
and 'tyS typeSpineF = (obj, 'tyS) typeSpineFF
and 'sTy syncTypeF = (asyncType, 'sTy) syncTypeFF
and 'o objF = (asyncType, spine, expObj, 'o) objFF
and 'sp spineF = (monadObj, 'sp) spineFF
and 'e expObjF = (obj, spine, monadObj, 'e) expObjFF
and 'm monadObjF = (obj, 'm) monadObjFF

and subst = subst'
and patSubst = subst'
and pat_Subst = subst'

and nfKind = kind
and nfAsyncType = asyncType
and nfTypeSpine = typeSpine
and nfSyncType = syncType
and nfObj = obj
and nfSpine = spine
and nfExpObj = expObj
and nfMonadObj = monadObj

and head = asyncType headF
and nfHead = (*nf*)asyncType headF

and apxKind = kind
and apxAsyncType = asyncType
and apxSyncType = syncType

and typeLogicVar = (*apx*)asyncType option ref * word

type 'a substi = subst'

datatype typeOrKind = Ty of asyncType | Ki of kind
datatype decl = ConstDecl of string * int * typeOrKind
	| TypeAbbrev of string * asyncType
	| ObjAbbrev of string * asyncType * obj
	| Query of int option * int option * int option * int * asyncType

datatype declError = TypeErr | KindErr | AmbigType | UndeclId | GeneralErr
exception ExnDeclError of declError * string

type 'ki nfKindF = (nfAsyncType, 'ki) kindFF
type 'aTy nfAsyncTypeF = (nfTypeSpine, nfSyncType, 'aTy) asyncTypeFF
type 'tyS nfTypeSpineF = (nfObj, 'tyS) typeSpineFF
type 'sTy nfSyncTypeF = (nfAsyncType, 'sTy) syncTypeFF
type 'o nfObjF = (nfSpine, nfExpObj, 'o) nfObjFF
type 'sp nfSpineF = (nfMonadObj, 'sp) spineFF
type 'e nfExpObjF = (nfSpine, nfMonadObj, 'e) nfExpObjFF
type 'm nfMonadObjF = (nfObj, 'm) monadObjFF

val NfKClos = KClos
val NfTClos = TClos
val NfTSClos = TSClos
val NfSTClos = STClos
val NfClos = Clos
val NfSClos = SClos
val NfEClos = EClos
val NfMClos = MClos

datatype ('aTy, 'ki) apxKindFF
	= ApxType
	| ApxKPi of 'aTy * 'ki
datatype ('sTy, 'aTy) apxAsyncTypeFF
	= ApxLolli of 'sTy * 'aTy
	| ApxAddProd of 'aTy * 'aTy
	| ApxTMonad of 'sTy
	| ApxTAtomic of string
	| ApxTAbbrev of string * asyncType
	| ApxTLogicVar of typeLogicVar
datatype ('aTy, 'sTy) apxSyncTypeFF
	= ApxTTensor of 'sTy * 'sTy
	| ApxTOne
	| ApxTDown of 'aTy
	| ApxTAffi of 'aTy
	| ApxTBang of 'aTy
type 'ki apxKindF = (apxAsyncType, 'ki) apxKindFF
type 'aTy apxAsyncTypeF = (apxSyncType, 'aTy) apxAsyncTypeFF
type 'sTy apxSyncTypeF = (apxAsyncType, 'sTy) apxSyncTypeFF

val redex = IntRedex
val nfredex = IntRedex
val nfletredex = IntLetRedex

fun nbinds (FixPattern (_, n)) = n

infix with'ty with's
fun {X, ty=_, s, ctx, cnstr, tag} with'ty ty' = {X=X, ty=ty', s=s, ctx=ctx, cnstr=cnstr, tag=tag}
fun {X, ty, s=_, ctx, cnstr, tag} with's s' = {X=X, ty=ty, s=s', ctx=ctx, cnstr=cnstr, tag=tag}

end (* structure Syn1 *)
open Syn1


structure Subst1 =
struct
	(*structure Subst' = SubstFun (structure Syn = Syn1 datatype substi = datatype substi)*)
	structure Subst' = SubstFun (
			type t = subObj
			datatype subst' = datatype subst'
			structure Syn = Syn1)
	open Subst'
	open Syn1
	fun dot (M, EtaTag (_, (m, n)), s) = Dot (Idx (modeDiv m M, n), s)
	  | dot (M, Clos (Clos (N, s'), s''), s) = dot (M, Clos (N, comp (s', s'')), s)
	  | dot (M, Clos (EtaTag (_, (m, n)), s'), s) = Dot (Clos' (Idx (modeDiv m M, n), s'), s)
	  | dot (M, ob, s) = Dot (Ob (M, ob), s)

	fun subI ob = dot (INT, ob, id)
	fun subL ob = dot (LIN, ob, id)
end

fun etaShortcut ob = case Subst1.subL ob of
	  Dot (Idx (ID, n), _) => SOME (Context.LIN, n)
	| Dot (Idx (AFF4LIN, n), _) => SOME (Context.AFF, n)
	| Dot (Idx (INT4LIN, n), _) => SOME (Context.INT, n)
	| _ => NONE

structure Signatur = SignaturFun (Syn1)

val lVarCnt = ref 0w0
fun nextLVarCnt () = (lVarCnt := (!lVarCnt) + 0w1 ; !lVarCnt)

val tyLVarCnt = ref 0w0
fun nextTyLVarCnt () = (tyLVarCnt := (!tyLVarCnt) + 0w1 ; !tyLVarCnt)

fun newTVar () = TLogicVar (ref NONE, nextTyLVarCnt ())
fun newApxTVar () = TLogicVar (ref NONE, nextTyLVarCnt ())
fun newLVarCtx ctx ty = FixObj (Atomic (LogicVar {X=vref NONE, ty=ty, s=Subst1.id, ctx=ref ctx,
											cnstr=vref [], tag=nextLVarCnt ()}, FixSpine Nil))
val newLVar = newLVarCtx NONE
val newNfLVar = newLVar
val newNfLVarCtx = newLVarCtx


structure Pattern =
struct
	type ('x, 'ix) t = ('x, 'ix) pattern
	type ('x, 'ix, 't) F = ('x, 'ix, 't) patternF
	fun pbinds (PDepTensor (p1, p2)) = nbinds p1 + nbinds p2
	  | pbinds POne = 0
	  | pbinds (PDown _) = 1
	  | pbinds (PAffi _) = 1
	  | pbinds (PBang _) = 1
	fun inj a = FixPattern (a, pbinds a)
	fun prj (FixPattern (a, _)) = a
	fun Fmap f (PDepTensor (p1, p2)) = PDepTensor (f p1, f p2)
	  | Fmap f POne = POne
	  | Fmap f (PDown x) = PDown x
	  | Fmap f (PAffi x) = PAffi x
	  | Fmap f (PBang x) = PBang x
end

structure OPatternRec = Rec (structure T = struct
	open Pattern type t = opattern type 'a F = (string, string, 'a) patternF end)
structure TPatternRec = Rec (structure T = struct
	open Pattern type t = tpattern type 'a F = (unit, string option, 'a) patternF end)

fun newTPattern p = TPatternRec.postorderMap (fn (PBang _) => PBang (SOME "") | P => P) p

(* structure Kind : TYP2 where type ('a, 't) F = ('a, 't) kindFF
		and type t = kind and type a = asyncType *)
structure Kind =
struct
	type t = kind type a = asyncType
	type ('a, 't) F = ('a, 't) kindFF
	fun inj k = FixKind k
	fun prj (FixKind k) = (*HashCons.nd*) k
	  | prj (KClos (KClos (k, s'), s)) = prj (KClos (k, Subst1.comp (s', s)))
	  | prj (KClos (FixKind k, s)) = Subst1.subKind ((*HashCons.nd*) k, s)
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
	  | prj (TSClos (TSClos (S, s'), s)) = prj (TSClos (S, Subst1.comp (s', s)))
	  | prj (TSClos (FixTypeSpine S, s)) = Subst1.subTypeSpine ((*HashCons.nd*) S, s)
	fun Fmap (g, f) TNil = TNil
	  | Fmap (g, f) (TApp (N, S)) = TApp (g N, f S)
	fun newTSpine' ki = case Kind.prj ki of
		  Type => inj TNil
		| KPi (_, A, K) => inj (TApp (newLVar (Apx A), newTSpine' K))
	val newTSpine = newTSpine' o Signatur.sigLookupKind
end
(* structure AsyncType : TYP3 where type ('a, 'b, 't) F = ('a, 'b, 't) asyncTypeFF
		and type t = asyncType and type a = typeSpine and type b = syncType *)
structure AsyncType =
struct
	type t = asyncType type a = typeSpine type b = syncType
	type ('a, 'b, 't) F = ('a, 'b, 't) asyncTypeFF
	fun inj a = FixAsyncType a
	fun Fmap' h ((g1, g2), f) (TLPi (p, A, B)) = TLPi (h p, g2 A, f B)
	  | Fmap' _ (g, f) (AddProd (A, B)) = AddProd (f A, f B)
	  | Fmap' _ ((g1, g2), f) (TMonad S) = TMonad (g2 S)
	  | Fmap' _ ((g1, g2), f) (TAtomic (a, ts)) = TAtomic (a, g1 a ts)
	  | Fmap' _ (g, f) (TAbbrev (a, A)) = TAbbrev (a, f A)
	fun Fmap ((g1, g2), f) a = Fmap' (fn x => x) ((fn _ => g1, g2), f) a 
	fun prjApx (TLogicVar (ref NONE, _)) = raise ExnDeclError (AmbigType, "")
	  | prjApx (TLogicVar (ref (SOME a), _)) = prjApx a
	  | prjApx (TClos (a, _)) = prjApx a
	  | prjApx (Apx a) = prjApx a
	  | prjApx (FixAsyncType A) = Fmap' newTPattern
				((fn a => fn _ => TypeSpine.newTSpine a, ApxS), Apx) ((*HashCons.nd*) A)
	fun prj (FixAsyncType a) = (*HashCons.nd*) a
	  | prj (TClos (TClos (a, s'), s)) = prj (TClos (a, Subst1.comp (s', s)))
	  | prj (TClos (FixAsyncType a, s)) = Subst1.subType ((*HashCons.nd*) a, s)
	  | prj (TClos (TLogicVar (ref NONE, _), _)) = raise ExnDeclError (AmbigType, "")
	  | prj (TClos (TLogicVar (ref (SOME a), _), s)) = Subst1.subType (prjApx a, s)
	  | prj (TClos (Apx a, s)) = Subst1.subType (prjApx a, s)
	  | prj (TLogicVar (ref NONE, _)) = raise ExnDeclError (AmbigType, "")
	  | prj (TLogicVar (ref (SOME a), _)) = prjApx a
	  | prj (Apx a) = prjApx a
end
(* structure SyncType : TYP2 where type ('a, 't) F = ('a, 't) syncTypeFF
		and type t = syncType and type a = asyncType *)
structure SyncType =
struct
	type t = syncType type a = asyncType
	type ('a, 't) F = ('a, 't) syncTypeFF
	fun Fmap' h (g, f) (LExists (p, S1, S2)) = LExists (h p, f S1, f S2)
	  | Fmap' _ (g, f) TOne = TOne
	  | Fmap' _ (g, f) (TDown A) = TDown (g A)
	  | Fmap' _ (g, f) (TAffi A) = TAffi (g A)
	  | Fmap' _ (g, f) (TBang A) = TBang (g A)
	fun Fmap gf a = Fmap' (fn x => x) gf a
	fun inj a = FixSyncType a
	fun prjApx (FixSyncType S) = Fmap' newTPattern (Apx, ApxS) ((*HashCons.nd*) S)
	  | prjApx (STClos (S, _)) = prjApx S
	  | prjApx (ApxS S) = prjApx S
	fun prj (FixSyncType a) = (*HashCons.nd*) a
	  | prj (STClos (STClos (S, s'), s)) = prj (STClos (S, Subst1.comp (s', s)))
	  | prj (STClos (FixSyncType S, s)) = Subst1.subSyncType ((*HashCons.nd*) S, s)
	  | prj (STClos (ApxS S, s)) = Subst1.subSyncType (prjApx S, s)
	  | prj (ApxS S) = prjApx S
end

(* structure Spine : TYP2 where type ('a, 't) F = ('a, 't) spineFF
		and type t = spine and type a = monadObj *)
structure Spine =
struct
	type t = spine type a = monadObj
	type ('a, 't) F = ('a, 't) spineFF
	fun inj a = FixSpine a
	fun prj (FixSpine a) = (*HashCons.nd*) a
	  | prj (SClos (SClos (S, s'), s)) = prj (SClos (S, Subst1.comp (s', s)))
	  | prj (SClos (FixSpine S, s)) = Subst1.subSpine ((*HashCons.nd*) S, s)
	fun Fmap (g, f) Nil = Nil
	  | Fmap (g, f) (LApp (M, S)) = LApp (g M, f S)
	  | Fmap (g, f) (ProjLeft S) = ProjLeft (f S)
	  | Fmap (g, f) (ProjRight S) = ProjRight (f S)
	fun appendSpine (S1', S2) = case prj S1' of
		  Nil => S2
		| LApp (M, S1) => inj (LApp (M, appendSpine (S1, S2)))
		| ProjLeft S1 => inj (ProjLeft (appendSpine (S1, S2)))
		| ProjRight S1 => inj (ProjRight (appendSpine (S1, S2)))
end
(* structure MonadObj : TYP2 where type ('a, 't) F = ('a, 't) monadObjFF
		and type t = monadObj and type a = obj *)
structure MonadObj =
struct
	type t = monadObj type a = obj
	type ('a, 't) F = ('a, 't) monadObjFF
	fun inj a = FixMonadObj a
	fun prj (FixMonadObj a) = (*HashCons.nd*) a
	  | prj (MClos (MClos (M, s'), s)) = prj (MClos (M, Subst1.comp (s', s)))
	  | prj (MClos (FixMonadObj M, s)) = Subst1.subMonadObj ((*HashCons.nd*) M, s)
	fun Fmap (g, f) (DepPair (M1, M2)) = DepPair (f M1, f M2)
	  | Fmap (g, f) One = One
	  | Fmap (g, f) (Down N) = Down (g N)
	  | Fmap (g, f) (Affi N) = Affi (g N)
	  | Fmap (g, f) (Bang N) = Bang (g N)
	  | Fmap _ MonUndef = MonUndef
	fun dotMonad (M, s) = case prj M of
		  DepPair (M1, M2) => dotMonad (M2, dotMonad (M1, s))
		| One => s
		| Down N => Subst1.dot (Context.LIN, N, s)
		| Affi N => Subst1.dot (Context.AFF, N, s)
		| Bang N => Subst1.dot (Context.INT, N, s)
		| MonUndef => Dot (Undef, s)
	fun subM m = dotMonad (m, Subst1.id)
end
(* structure Obj : TYP4 where type ('a, 'b, 'c, 't) F = ('a, 'b, 'c, 't) objFF
		and type t = obj and type a = asyncType and type b = spine and type c = expObj *)
structure Obj =
struct
	fun tryLVarAtomic (LogicVar {X, s, ...}, S) =
			Option.map (fn N => (Clos (N, s), S)) (!!X)
	  | tryLVarAtomic _ = NONE
	fun tryLVar (Atomic hS) = tryLVarAtomic hS
	  | tryLVar _ = NONE
	type t = obj type a = asyncType type b = spine type c = expObj
	type ('a, 'b, 'c, 't) F = ('a, 'b, 'c, 't) objFF
	fun inj a = FixObj a
	fun prj (FixObj N) = let val N = (*HashCons.nd*) N
			in case tryLVar N of NONE => N | SOME obS => intRedex obS end
	  | prj (Clos (Clos (N, s'), s)) = prj (Clos (N, Subst1.comp (s', s)))
	  | prj (Clos (FixObj N, s)) = let val N = (*HashCons.nd*) N
	  		in case tryLVar N of
				  NONE => Subst1.subObj intRedex (N, s)
				| SOME (ob, S) => intRedex (Clos (ob, s), SClos (S, s)) end
	  | prj (Clos (EtaTag (N, _), s)) = prj (Clos (N, s))
	  | prj (Clos (IntRedex (N, S), s)) = intRedex (Clos (N, s), SClos (S, s))
	  | prj (EtaTag (N, _)) = prj N
	  | prj (IntRedex (N, S)) = intRedex (N, S)
	and intRedex (ob, sp) = case (prj ob, Spine.prj sp) of
		  (N, Nil) => N
		| (LLam (_, N), LApp (M, S)) => intRedex (Clos (N, MonadObj.subM M), S)
		| (AddPair (N, _), ProjLeft S) => intRedex (N, S)
		| (AddPair (_, N), ProjRight S) => intRedex (N, S)
		| (Atomic (H, S1), S2) => Atomic (H, Spine.appendSpine (S1, Spine.inj S2))
		| (Redex (N, A, S1), S2) => Redex (N, A, Spine.appendSpine (S1, Spine.inj S2))
		| (Constraint (N, A), S) => intRedex (N, Spine.inj S)
		| _ => raise Fail "Internal error: intRedex"
	fun Fmap (g, f) (LLam (p, N)) = (LLam (p, f N))
	  | Fmap (g, f) (AddPair (N1, N2)) = (AddPair (f N1, f N2))
	  | Fmap ((g1, g2, g3), f) (Monad E) = Monad (g3 E)
	  | Fmap ((g1, g2, g3), f) (Atomic (h, S)) = Atomic (h, g2 S)
	  | Fmap ((g1, g2, g3), f) (Redex (N, A, S)) = Redex (f N, A, g2 S)
	  | Fmap ((g1, g2, g3), f) (Constraint (N, A)) = Constraint (f N, g1 A)
end
(* structure ExpObj : TYP4 where type ('a, 'b, 'c, 't) F = ('a, 'b, 'c, 't) expObjFF
		and type t = expObj and type a = obj and type b = spine and type c = monadObj *)
structure ExpObj =
struct
	fun tryLVar (Let (p, hS, E)) =
		Option.map (fn NS => (p, IntRedex NS, E)) (Obj.tryLVarAtomic hS)
	  | tryLVar _ = NONE
	type t = expObj type a = obj type b = spine type c = monadObj
	type ('a, 'b, 'c, 't) F = ('a, 'b, 'c, 't) expObjFF
	fun inj a = FixExpObj a
	fun prj (FixExpObj E) = (case tryLVar E of NONE => E | SOME pNE => intLetRedex pNE)
	  | prj (EClos (EClos (E, s'), s)) = prj (EClos (E, Subst1.comp (s', s)))
	  | prj (EClos (FixExpObj E, s)) = (case tryLVar E of
			  NONE => Subst1.subExpObj intLetRedex' ((*HashCons.nd*) E, s)
			| SOME pNE => prj (EClos (IntLetRedex pNE, s)))
	  | prj (IntLetRedex pNE) = intLetRedex pNE
	  | prj (EClos (IntLetRedex (p, N, E), s)) =
			intLetRedex (p, Clos (N, s), EClos (E, Subst1.dotn (nbinds p) s))
	and intLetRedex' (p, NS, E) = intLetRedex (p, IntRedex NS, E)
	and intLetRedex (p, ob, E) = case Obj.prj ob of
		  Atomic hS => Let (p, hS, E)
		| Constraint (N, A) => intLetRedex (p, N, E)
		| Redex (N, _, S) => intLetRedex' (p, (N, S), E)
		| Monad E' => (case prj E' of
			  Mon M => prj (EClos (E, MonadObj.subM M))
			| Let (q, hS, E'') => Let (q, hS, IntLetRedex (p, Obj.inj $ Monad E'',
						EClos (E, Subst1.dotn (nbinds p) (Subst1.shift (nbinds q)))))
			| LetRedex (q, S, N, E'') => LetRedex (q, S, N, IntLetRedex (p, Obj.inj $ Monad E'',
						EClos (E, Subst1.dotn (nbinds p) (Subst1.shift (nbinds q))))))
		| _ => raise Fail "Internal error: intLetRedex"
	fun Fmap ((g1, g2, g3), f) (LetRedex (p, S, N, E)) = LetRedex (p, S, g1 N, f E)
	  | Fmap ((g1, g2, g3), f) (Let (p, (h, S), E)) = Let (p, (h, g2 S), f E)
	  | Fmap ((g1, g2, g3), f) (Mon M) = Mon (g3 M)
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

structure Subst =
struct
	open Subst1
	val subM = MonadObj.subM
	val dotMonad = MonadObj.dotMonad
end

val Type' = Kind.inj Type
val KPi' = Kind.inj o KPi
val TLPi' = AsyncType.inj o TLPi
val AddProd' = AsyncType.inj o AddProd
val TMonad' = AsyncType.inj o TMonad
val TAtomic' = AsyncType.inj o TAtomic
val TAbbrev' = AsyncType.inj o TAbbrev
val TNil' = TypeSpine.inj TNil
val TApp' = TypeSpine.inj o TApp
val LExists' = SyncType.inj o LExists
val TOne' = SyncType.inj TOne
val TDown' = SyncType.inj o TDown
val TAffi' = SyncType.inj o TAffi
val TBang' = SyncType.inj o TBang
val LLam' = Obj.inj o LLam
val AddPair' = Obj.inj o AddPair
val Monad' = Obj.inj o Monad
val Atomic' = Obj.inj o Atomic
val Redex' = Obj.inj o Redex
val Constraint' = Obj.inj o Constraint
val Nil' = Spine.inj Nil
val LApp' = Spine.inj o LApp
val ProjLeft' = Spine.inj o ProjLeft
val ProjRight' = Spine.inj o ProjRight
val LetRedex' = ExpObj.inj o LetRedex
val Let' = ExpObj.inj o Let
val Mon' = ExpObj.inj o Mon
val DepPair' = MonadObj.inj o DepPair
val One' = MonadObj.inj One
val Down' = MonadObj.inj o Down
val Affi' = MonadObj.inj o Affi
val Bang' = MonadObj.inj o Bang
val MonUndef' = MonadObj.inj MonUndef
fun PDepTensor' x = Pattern.inj $ PDepTensor x
val POne' = (*Pattern.inj POne*) FixPattern (POne, 0)
fun PDown' x = Pattern.inj $ PDown x
fun PAffi' x = Pattern.inj $ PAffi x
fun PBang' x = Pattern.inj $ PBang x

val appendSpine = Spine.appendSpine

end (* structure Syn2 *)
open Syn2


(*structure Whnf = WhnfFun (Syn2)*)

(* structure NfKind : TYP2 where type ('a, 't) F = ('a, 't) kindFF
		and type t = nfKind and type a = nfAsyncType *)
(* structure NfAsyncType : TYP3 where type ('a, 'b, 't) F = ('a, 'b, 't) asyncTypeFF
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
	fun inj (NfLLam pN) = FixObj (LLam pN)
	  | inj (NfAddPair N1N2) = FixObj (AddPair N1N2)
	  | inj (NfMonad E) = FixObj (Monad E)
	  | inj (NfAtomic at) = FixObj (Atomic at)
	fun prj N = case Obj.prj N of
		  LLam pN => NfLLam pN
		| AddPair N1N2 => NfAddPair N1N2
		| Atomic hS => NfAtomic hS
		| Monad E => NfMonad E
		| Redex (N, _, S) => prj (IntRedex (N, S))
		| Constraint (N, _) => prj N
	fun Fmap (g, f) (NfLLam (p, N)) = NfLLam (p, f N)
	  | Fmap (g, f) (NfAddPair (N1, N2)) = NfAddPair (f N1, f N2)
	  | Fmap ((g1, g2), f) (NfMonad E) = NfMonad (g2 E)
	  | Fmap ((g1, g2), f) (NfAtomic (h, S)) = NfAtomic (h, g1 S)
end
(* structure NfExpObj : TYP3 where type ('a, 'b, 't) F = ('a, 'b, 't) nfExpObjFF
		and type t = nfExpObj and type a = nfSpine and type b = nfMonadObj *)
structure NfExpObj =
struct
	type t = nfExpObj type a = nfSpine type b = nfMonadObj
	type ('a, 'b, 't) F = ('a, 'b, 't) nfExpObjFF
	fun inj (NfLet phSE) = FixExpObj (Let phSE)
	  | inj (NfMon M) = FixExpObj (Mon M)
	fun prj E = case ExpObj.prj E of
		  LetRedex (p, _, N, E) => prj (IntLetRedex (p, N, E))
		| Let phSE => NfLet phSE
		| Mon M => NfMon M
	fun Fmap ((g1, g2), f) (NfLet (p, (h, S), E)) = NfLet (p, (h, g1 S), f E)
	  | Fmap ((g1, g2), f) (NfMon M) = NfMon (g2 M)
end
(* structure NfSpine : TYP2 where type ('a, 't) F = ('a, 't) spineFF
		and type t = nfSpine and type a = nfObj *)
(* structure NfMonadObj : TYP2 where type ('a, 't) F = ('a, 't) monadObjFF
		and type t = nfMonadObj and type a = nfObj *)
structure NfSpine = Spine
structure NfMonadObj = MonadObj

structure NfInj =
struct
	val Type' = NfKind.inj Type
	val KPi' = NfKind.inj o KPi
	val TLPi' = NfAsyncType.inj o TLPi
	val AddProd' = NfAsyncType.inj o AddProd
	val TMonad' = NfAsyncType.inj o TMonad
	val TAtomic' = NfAsyncType.inj o TAtomic
	val TAbbrev' = NfAsyncType.inj o TAbbrev
	val TNil' = NfTypeSpine.inj TNil
	val TApp' = NfTypeSpine.inj o TApp
	val LExists' = NfSyncType.inj o LExists
	val TOne' = NfSyncType.inj TOne
	val TDown' = NfSyncType.inj o TDown
	val TAffi' = NfSyncType.inj o TAffi
	val TBang' = NfSyncType.inj o TBang
	val Nil' = NfSpine.inj Nil
	val LApp' = NfSpine.inj o LApp
	val ProjLeft' = NfSpine.inj o ProjLeft
	val ProjRight' = NfSpine.inj o ProjRight
	val DepPair' = NfMonadObj.inj o DepPair
	val One' = NfMonadObj.inj One
	val Down' = NfMonadObj.inj o Down
	val Affi' = NfMonadObj.inj o Affi
	val Bang' = NfMonadObj.inj o Bang
	val MonUndef' = NfMonadObj.inj MonUndef
end

val NfLLam' = NfObj.inj o NfLLam
val NfAddPair' = NfObj.inj o NfAddPair
val NfMonad' = NfObj.inj o NfMonad
val NfAtomic' = NfObj.inj o NfAtomic
val NfLet' = NfExpObj.inj o NfLet
val NfMon' = NfExpObj.inj o NfMon


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
(* structure ApxSyncType : TYP2 where type ('a, 't) F = ('a, 't) apxSyncTypeFF
		and type t = apxSyncType and type a = apxAsyncType *)
structure ApxSyncType =
struct
	type t = apxSyncType type a = apxAsyncType
	type ('a, 't) F = ('a, 't) apxSyncTypeFF
	fun prj (STClos (S, _)) = prj S
	  | prj (ApxS S) = prj S
	  | prj s = case SyncType.prj s of
		  LExists (p, S1, S2) => ApxTTensor (S1, S2)
		| TOne => ApxTOne
		| TDown A => ApxTDown A
		| TAffi A => ApxTAffi A
		| TBang A => ApxTBang A
	fun s2p (ApxTTensor x) = PDepTensor x
	  | s2p ApxTOne = POne
	  | s2p (ApxTDown x) = PDown ()
	  | s2p (ApxTAffi x) = PAffi ()
	  | s2p (ApxTBang x) = PBang (SOME "")
	fun syncType2TPattern s = TPatternRec.unfold (s2p o prj) s
	fun inj (ApxTTensor (S1, S2)) = SyncType.inj (LExists (syncType2TPattern S1, S1, S2))
	  | inj ApxTOne = SyncType.inj TOne
	  | inj (ApxTDown A) = SyncType.inj (TDown A)
	  | inj (ApxTAffi A) = SyncType.inj (TAffi A)
	  | inj (ApxTBang A) = SyncType.inj (TBang A)
	fun Fmap (g, f) (ApxTTensor (S1, S2)) = ApxTTensor (f S1, f S2)
	  | Fmap (g, f) ApxTOne = ApxTOne
	  | Fmap (g, f) (ApxTDown A) = ApxTDown (g A)
	  | Fmap (g, f) (ApxTAffi A) = ApxTAffi (g A)
	  | Fmap (g, f) (ApxTBang A) = ApxTBang (g A)
end
(* structure ApxAsyncType : TYP2 where type ('a, 't) F = ('a, 't) apxAsyncTypeFF
		and type t = apxAsyncType and type a = apxSyncType *)
structure ApxAsyncType =
struct
	type t = apxAsyncType type a = syncType
	type ('a, 't) F = ('a, 't) apxAsyncTypeFF
	fun inj (ApxLolli (S, A)) = AsyncType.inj (TLPi (ApxSyncType.syncType2TPattern S, S, A))
	  | inj (ApxAddProd (A, B)) = AsyncType.inj (AddProd (A, B))
	  | inj (ApxTMonad S) = AsyncType.inj (TMonad S)
	  | inj (ApxTAtomic a) = AsyncType.inj (TAtomic (a, TypeSpine.inj TNil))
	  | inj (ApxTAbbrev aA) = AsyncType.inj (TAbbrev aA)
	  | inj (ApxTLogicVar X) = TLogicVar X
	fun prj (TLogicVar (ref (SOME A), _)) = prj A
	  | prj (TLogicVar (X as (ref NONE, _))) = ApxTLogicVar X
	  | prj (TClos (A, _)) = prj A
	  | prj (Apx A) = prj A
	  | prj a = case AsyncType.prj a of
		  TLPi (_, S, A) => ApxLolli (S, A)
		| AddProd (A, B) => ApxAddProd (A, B)
		| TMonad S => ApxTMonad S
		| TAtomic (a, _) => ApxTAtomic a
		| TAbbrev (a, A) => ApxTAbbrev (a, A)
	fun Fmap (g, f) (ApxLolli (S, A)) = ApxLolli (g S, f A)
	  | Fmap (g, f) (ApxAddProd (A, B)) = ApxAddProd (f A, f B)
	  | Fmap (g, f) (ApxTMonad S) = ApxTMonad (g S)
	  | Fmap (g, f) (ApxTAtomic a) = ApxTAtomic a
	  | Fmap (g, f) (ApxTAbbrev aA) = ApxTAbbrev aA
	  | Fmap (g, f) (ApxTLogicVar X) = ApxTLogicVar X
end

val ApxType' = ApxKind.inj ApxType
val ApxKPi' = ApxKind.inj o ApxKPi
val ApxLolli' = ApxAsyncType.inj o ApxLolli
val ApxAddProd' = ApxAsyncType.inj o ApxAddProd
val ApxTMonad' = ApxAsyncType.inj o ApxTMonad
val ApxTAtomic' = ApxAsyncType.inj o ApxTAtomic
val ApxTAbbrev' = ApxAsyncType.inj o ApxTAbbrev
val ApxTLogicVar' = ApxAsyncType.inj o ApxTLogicVar
val ApxTTensor' = ApxSyncType.inj o ApxTTensor
val ApxTOne' = ApxSyncType.inj ApxTOne
val ApxTDown' = ApxSyncType.inj o ApxTDown
val ApxTAffi' = ApxSyncType.inj o ApxTAffi
val ApxTBang' = ApxSyncType.inj o ApxTBang

structure ApxKindRec = Rec2 (structure T = ApxKind)
structure ApxAsyncTypeRec = Rec2 (structure T = ApxAsyncType)
structure ApxSyncTypeRec = Rec2 (structure T = ApxSyncType)

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

(* updLVar : typeLogicVar * apxAsyncType -> unit *)
fun updLVar ((ref (SOME _), _), _) = raise Fail "Internal error: typeLogicVar already updated"
  | updLVar ((X as ref NONE, _), A) = X := SOME A

(* isUnknown : asyncType -> bool *)
fun isUnknown (TClos (A, _)) = isUnknown A
  | isUnknown (FixAsyncType _) = false
  | isUnknown (TLogicVar (ref (SOME A), _)) = isUnknown A
  | isUnknown (TLogicVar (ref NONE, _)) = true
  | isUnknown (Apx A) = isUnknown A

fun kindToApx x = x
fun asyncTypeToApx x = x
fun syncTypeToApx x = x

fun nfKindToApx x = x
fun nfAsyncTypeToApx x = x
fun nfSyncTypeToApx x = x

fun injectApxType x = Apx x
fun injectApxSyncType x = ApxS x
fun unsafeCast x = x
fun unsafeCastS x = x

fun normalizeKind x = x
fun normalizeType x = x
fun normalizeObj x = x
fun normalizeExpObj x = x
fun normalizeMonadObj x = x
fun normalizeHead x = x

fun unnormalizeKind x = x
fun unnormalizeType x = x
fun unnormalizeSyncType x = x
fun unnormalizeObj x = x
fun unnormalizeExpObj x = x

end
