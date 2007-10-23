structure ImplicitVars :> IMPLICITVARS =
struct

open VRef infix ::=
open Syntax
open SymbTable
open Context

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
				val () = Util.objAppType
							(fn Atomic (UCVar x, _, _) => ucs := x::(!ucs) | _ => ()) ty
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
	let fun Idx A n = Atomic' (Var n, asyncTypeToApx A, Nil') (* stub: Eta expand *)
		fun sh ty = TClos (ty, Subst.shift 1)
	in case ctx of
		  [] => Atomic' (newUCVar B, asyncTypeToApx B, S)
		| (x, A, UN)::ctx => raiseLVar' (ctx, TPi' (x, A, B), App' (Idx A n, S), n+1)
		| (x, A, LIN)::ctx => raiseLVar' (ctx, Lolli' (A, sh B), LinApp' (Idx A n, S), n+1)
		| (x, A, NO)::ctx => raiseLVar' (ctx, sh B, S, n+1)
	end

fun raiseLVar (Atomic (LogicVar {X, ty, s, ctx, tag, ...}, _, _)) = (case (!!X, !ctx) of
	  (SOME _, _) => () (* this can never occur?? --asn *)
	| (NONE, NONE) => raise Fail ("Internal error: no context on $"^(Int.toString tag)^"\n")
	| (NONE, SOME ctx) => X ::= SOME (raiseLVar' (ctx2list ctx, TClos (ty, s), Nil', 1)) )
						(* stub: bug??? ctx |- A : Type or ctx |- A[s] : Type ??? --asn *)
  | raiseLVar _ = ()

(* logicVarsToUCVarsObj : obj -> unit *)
fun logicVarsToUCVarsObj ob = Util.objAppObj raiseLVar ob

(* logicVarsToUCVarsType : asyncType -> unit *)
fun logicVarsToUCVarsType ty = Util.objAppType raiseLVar ty

(* logicVarsToUCVarsKind : kind -> unit *)
fun logicVarsToUCVarsKind ki = Util.objAppKind raiseLVar ki


fun uc2bKind lookup n ki = case Kind.prj ki of
	  Type => Type'
	| KPi (x, A, K) => KPi' (x, uc2bType lookup n A, uc2bKind lookup (n+1) K)
and uc2bType lookup n ty = case AsyncType.prj ty of
	  Lolli (A, B) => Lolli' (uc2bType lookup n A, uc2bType lookup n B)
	| TPi (x, A, B) => TPi' (x, uc2bType lookup n A, uc2bType lookup (n+1) B)
	| AddProd (A, B) => AddProd' (uc2bType lookup n A, uc2bType lookup n B)
	| Top => Top'
	| TMonad S => TMonad' (uc2bSyncType lookup n S)
	| TAtomic (a, impl, S) => TAtomic' (a, map (uc2bObj lookup n) impl, uc2bTypeSpine lookup n S)
	| TAbbrev aA => TAbbrev' aA
	| TUnknown => raise Fail "Internal error: uc2bType\n"
and uc2bTypeSpine lookup n sp = case TypeSpine.prj sp of
	  TNil => TNil'
	| TApp (N, S) => TApp' (uc2bObj lookup n N, uc2bTypeSpine lookup n S)
and uc2bSyncType lookup n sty = case SyncType.prj sty of
	  TTensor (S1, S2) => TTensor' (uc2bSyncType lookup n S1, uc2bSyncType lookup n S2)
	| TOne => TOne'
	| Exists (x, A, S) => Exists' (x, uc2bType lookup n A, uc2bSyncType lookup (n+1) S)
	| Async A => Async' (uc2bType lookup n A)
and uc2bObj lookup n ob = case Obj.prj ob of
	  LinLam (x, N) => LinLam' (x, uc2bObj lookup (n+1) N)
	| Lam (x, N) => Lam' (x, uc2bObj lookup (n+1) N)
	| AddPair (N1, N2) => AddPair' (uc2bObj lookup n N1, uc2bObj lookup n N2)
	| Unit => Unit'
	| Monad E => Monad' (uc2bExp lookup n E)
	| Atomic (H, A, S) => Atomic' (uc2bHead lookup n H, A, uc2bSpine lookup n S)
	| Redex (N, A, S) => Redex' (uc2bObj lookup n N, A, uc2bSpine lookup n S)
	| Constraint (N, A) => Constraint' (uc2bObj lookup n N, uc2bType lookup n A)
and uc2bHead lookup n h = case h of
	  Const (c, impl) => Const (c, map (uc2bObj lookup n) impl)
	| UCVar v => Var (lookup n v)
	| LogicVar _ => raise Fail "Internal error: uc2bHead\n"
	| Var vn => Var vn
and uc2bSpine lookup n sp = case Spine.prj sp of
	  Nil => Nil'
	| App (N, S) => App' (uc2bObj lookup n N, uc2bSpine lookup n S)
	| LinApp (N, S) => LinApp' (uc2bObj lookup n N, uc2bSpine lookup n S)
	| ProjLeft S => ProjLeft' (uc2bSpine lookup n S)
	| ProjRight S => ProjRight' (uc2bSpine lookup n S)
and uc2bExp lookup n e = case ExpObj.prj e of
	  Let (p, N, E) => Let' (uc2bPattern lookup n p, uc2bObj lookup n N, uc2bExp lookup (n + nbinds p) E)
	| Mon M => Mon' (uc2bMonadObj lookup n M)
and uc2bMonadObj lookup n m = case MonadObj.prj m of
	  Tensor (M1, M2) => Tensor' (uc2bMonadObj lookup n M1, uc2bMonadObj lookup n M2)
	| One => One'
	| DepPair (N, M) => DepPair' (uc2bObj lookup n N, uc2bMonadObj lookup n M)
	| Norm N => Norm' (uc2bObj lookup n N)
and uc2bPattern lookup n p = case Pattern.prj p of
	  PTensor (p1, p2) => PTensor' (uc2bPattern lookup n p1, uc2bPattern lookup n p2)
	| POne => POne'
	| PDepPair (x, A, p) => PDepPair' (x, uc2bType lookup n A, uc2bPattern lookup (n+1) p)
	| PVar (x, A) => PVar' (x, uc2bType lookup n A)


fun ctx2Lookup ctx =
	let fun l [] n x = raise Fail "Internal error: UCVar not in implicits\n"
		  | l ((y, _)::ys) n x = if x=y then n else l ys (n+1) x
	in l ctx end

(* convertUCVarsKind : implicits -> kind -> kind *)
fun convertUCVarsKind imp ki = uc2bKind (ctx2Lookup (rev imp)) 1 ki

(* convertUCVarsType : implicits -> asyncType -> asyncType *)
fun convertUCVarsType imp ty = uc2bType (ctx2Lookup (rev imp)) 1 ty

(* convertUCVarsImps : implicits -> implicits *)
fun convertUCVarsImps imp =
	let fun conv [] imps = imps
		  | conv ((x, A)::ctx) imps = conv ctx ((x, uc2bType (ctx2Lookup ctx) 1 A)::imps)
	in conv (rev imp) [] end

end
