structure ImplicitVars :> IMPLICITVARS =
struct

open VRef infix ::=
open Syntax infix with'ty with's
open SymbTable
open Context

type implicits = (string * asyncType) list

val ucTable = ref (empty ()) : asyncType Table ref

val newint = ref 0
fun newname () = (newint := 1 + !newint; "xx" ^ Int.toString (!newint))
fun freshname () =
	let val v = newname ()
	in if isSome (peek (!ucTable, v)) then freshname () else v end

fun newUCVar ty = let val v = freshname () in ucTable := insert (!ucTable, v, ty); UCVar v end

(* resetUCTable : unit -> unit *)
fun resetUCTable () = ucTable := empty ()

(* mapUCTable : (asyncType -> asyncType) -> unit *)
fun mapUCTable f = ucTable := mapTable f (!ucTable)

(* appUCTable : (asyncType -> unit) -> unit *)
fun appUCTable f = appTable f (!ucTable)

(* noUCVars : unit -> unit *)
fun noUCVars () = if null (toList (!ucTable)) then () else raise Fail "UCVars not allowed\n"

(* apxUCLookup : string -> apxAsyncType *)
fun apxUCLookup x =
	case peek (!ucTable, x) of
		  NONE => let val A = newTVar() in ucTable := insert (!ucTable, x, A); asyncTypeToApx A end
		| SOME A => asyncTypeToApx A

(* ucLookup : string -> asyncType *)
fun ucLookup x = valOf (peek (!ucTable, x))

(* sort : unit -> implicits *)
fun sort () =
	let fun getUCvars ty =
			let val ucs = ref []
				fun collect t = Util.objAppType
							(fn Atomic (UCVar x, ()) => ucs := x::(!ucs)
							  | Atomic (LogicVar {ty, s, ...}, ()) => collect (TClos (ty, s))
							  | _ => ()) t
				val () = collect ty
			in !ucs end
		fun listToSet l = foldl (fn (x, s) => insert (s, x, ())) (empty ()) l
		val ucVars = toList (!ucTable)
		val graph = foldl
				(fn ((x, _), g) => insert (g, x, (ref (empty ()), ref (empty ()))))
				(empty ()) ucVars
		fun outs x = #2 (valOf (peek (graph, x)))
		fun ins x = #1 (valOf (peek (graph, x)))
		val () = List.app
				(fn (x, A) =>
					let val dependencies = getUCvars A
						val xIn = ins x
						val () = xIn := listToSet dependencies
						val () = List.app
								(fn y =>
									let val yOut = outs y
									in yOut := insert (!yOut, x, ()) end)
								dependencies
					in () end)
				ucVars
		val noIns = map #1 (List.filter
								(fn (_, (ref inset, _)) => 0 = numItems inset)
								(toList graph))
		fun topsort l [] = rev l
		  | topsort l (x::xs) =
				topsort ((x, ucLookup x)::l)
					(xs @ foldl
						(fn ((y, ()), xs) =>
							let val yIn = ins y
								val () = yIn := delete (!yIn, x)
							in if numItems (!yIn) = 0 then y::xs else xs end)
						[] ((toList o ! o outs) x))
	in topsort [] noIns end

(* ctx |- B : Type
   ctx |- X : B *)
fun raiseLVar' (ctx, B, S, n) =
	let fun Idx A n = Atomic' (Var n, Nil') (* stub: Eta expand *)
		fun sh ty = TClos (ty, Subst.shift 1)
	in case ctx of
		  [] => Atomic' (newUCVar B, S)
		| (x, A, UN)::ctx => raiseLVar' (ctx, TPi' (SOME x, A, B), App' (Idx A n, S), n+1)
		| (x, A, LIN)::ctx => raiseLVar' (ctx, Lolli' (A, sh B), LinApp' (Idx A n, S), n+1)
		| (x, A, NO)::ctx => raiseLVar' (ctx, sh B, S, n+1)
	end

fun raiseLVar (Atomic (LogicVar {X, ty, ctx, tag, ...}, ())) = (case (!!X, !ctx) of
	  (SOME _, _) => () (* this can never occur?? --asn *)
	| (NONE, NONE) => raise Fail ("Internal error: no context on $"^(Word.toString tag)^"\n")
	| (NONE, SOME ctx) => X ::= SOME (raiseLVar' (ctx2list ctx, ty, Nil', 1)) )
	(*| (NONE, SOME ctx) => X ::= SOME (raiseLVar' (ctx2list ctx, TClos (ty, s), Nil', 1))*)
						(* stub: bug??? ctx |- A : Type or ctx |- A[s] : Type ??? --asn *)
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
	  Lolli (A, B) => Lolli' (uc2xType lookup n A, uc2xType lookup n B)
	| TPi (x, A, B) => TPi' (x, uc2xType lookup n A, uc2xType lookup (depInc x n) B)
	| AddProd (A, B) => AddProd' (uc2xType lookup n A, uc2xType lookup n B)
	| Top => Top'
	| TMonad S => TMonad' (uc2xSyncType lookup n S)
	| TAtomic (a, S) => TAtomic' (a, uc2xTypeSpine lookup n S)
	| TAbbrev aA => TAbbrev' aA
and uc2xTypeSpine lookup n sp = Util.TypeSpineRec.unfold (uc2xObj lookup n) TypeSpine.prj sp
and uc2xSyncType lookup n sty = case SyncType.prj sty of
	  TTensor (S1, S2) => TTensor' (uc2xSyncType lookup n S1, uc2xSyncType lookup n S2)
	| TOne => TOne'
	| Exists (x, A, S) => Exists' (x, uc2xType lookup n A, uc2xSyncType lookup (depInc x n) S)
	| Async A => Async' (uc2xType lookup n A)
and uc2xObj lookup n ob = case Obj.prj ob of
	  LinLam (x, N) => LinLam' (x, uc2xObj lookup (n+1) N)
	| Lam (x, N) => Lam' (x, uc2xObj lookup (n+1) N)
	| AddPair (N1, N2) => AddPair' (uc2xObj lookup n N1, uc2xObj lookup n N2)
	| Unit => Unit'
	| Monad E => Monad' (uc2xExp lookup n E)
	| Atomic (H, S) => Atomic' (uc2xHead lookup n H, uc2xSpine lookup n S)
	| Redex (N, A, S) => Redex' (uc2xObj lookup n N, A, uc2xSpine lookup n S)
	| Constraint (N, A) => Constraint' (uc2xObj lookup n N, uc2xType lookup n A)
and uc2xHead lookup n h = case h of
	  Const c => Const c
	| UCVar v => lookup n v
	| LogicVar X =>
		LogicVar (X with'ty uc2xType lookup n (#ty X) with's Subst.map (uc2xObj lookup n) (#s X))
	| Var vn => Var vn
and uc2xSpine lookup n sp = Util.SpineRec.unfold (uc2xObj lookup n) Spine.prj sp
and uc2xExp lookup n e = case ExpObj.prj e of
	  Let (p, N, E) => Let' (uc2xPattern lookup n p, uc2xObj lookup n N, uc2xExp lookup (n + nbinds p) E)
	| Mon M => Mon' (uc2xMonadObj lookup n M)
and uc2xMonadObj lookup n m = Util.MonadObjRec.unfold (uc2xObj lookup n) MonadObj.prj m
and uc2xPattern lookup n p = case Pattern.prj p of
	  PTensor (p1, p2) => PTensor' (uc2xPattern lookup n p1, uc2xPattern lookup n p2)
	| POne => POne'
	| PDepPair (x, A, p) => PDepPair' (x, uc2xType lookup n A, uc2xPattern lookup (n+1) p)
	| PVar (x, A) => PVar' (x, uc2xType lookup n A)


fun ctx2Lookup ctx =
	let fun l [] n x = raise Fail "Internal error: UCVar not in implicits\n"
		  | l ((y, _)::ys) n x = if x=y then Var n else l ys (n+1) x
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
	let val table = mapTable (fn A => newLVarCtx (SOME emptyCtx) A) (!ucTable)
		fun uc2lvar n x = case Obj.prj (Clos (valOf (peek (table, x)), Subst.shift n)) of
			  Atomic (X as LogicVar _, _) => X
			| _ => raise Fail "Internal error: uc2lvar\n"
	in (uc2xType uc2lvar 0 ty, toList table) end

end
