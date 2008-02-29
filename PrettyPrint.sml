structure PrettyPrint :> PRETTYPRINT =
struct

open Syntax infix with'ty

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
	let fun eq x y = x=y
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
	| Top => ["T"]
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
	  TTensor (S1, S2) => paren pa (pSyncType ctx true S1 @ [" @ "] @ pSyncType ctx true S2)
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
	  Tensor (M1, M2) => paren pa (pMonadObj ctx true M1 @ [" @ "] @ pMonadObj ctx true M2)
	| One => ["1"]
	| DepPair (N, M) => ["["] @ pObj ctx false N @ [", "] @ pMonadObj ctx false M @ ["]"]
	| Norm N => pObj ctx pa N
and pPattern ctx bctx pa p = case Pattern.prj p of
	  PTensor (p1, p2) =>
			let val (pP1, bctx') = pPattern ctx bctx true p1
				val (pP2, bctx'') = pPattern ctx bctx' true p2
			in (paren pa (pP1 @ [" @ "] @ pP2), bctx'') end
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

type intset = int list
val empty = []
fun occur n = [n]
fun decrn n is = List.filter (fn x => x>=1) (map (fn x => x-n) is)
fun decr is = decrn 1 is
fun depend is = List.exists (fn x => x=1) is
fun union (is1, is2) = is1 @ is2
fun occurFromTo a b = if a <= b then a::occurFromTo (a+1) b else []

fun join2 f (a1, occ1) (a2, occ2) = (f (a1, a2), union (occ1, occ2))
fun joinDep clo f NONE (a1, occ1) (a2, occ2) = (f (NONE, a1, a2), union (occ1, occ2))
  | joinDep clo f (SOME x) (a1, occ1) (a2, occ2) =
		if depend occ2 then (f (SOME x, a1, a2), union (occ1, decr occ2))
		else (f (NONE, a1, clo (a2, Subst.invert (Subst.shift 1))), union (occ1, decr occ2))

fun rdKind ki = case Kind.prj ki of
	  Type => (Type', empty)
	| KPi (x, A, K) => joinDep KClos KPi' x (rdType A) (rdKind K)
and rdType ty = case AsyncType.prj ty of
	  Lolli (A, B) => join2 Lolli' (rdType A) (rdType B)
	| TPi (x, A, B) => joinDep TClos TPi' x (rdType A) (rdType B)
	| AddProd (A, B) => join2 AddProd' (rdType A) (rdType B)
	| Top => (Top', empty)
	| TMonad S => Util.map1 TMonad' (rdSyncType S)
	| TAtomic (a, S) => Util.map1 (fn S' => TAtomic' (a, S')) (rdTypeSpine S)
(*			let val (impl', occs) = ListPair.unzip (map rdObj impl)
				val (S', occS) = rdTypeSpine S
			in (TAtomic' (a, impl', S'), foldl union occS occs) end*)
	| TAbbrev (a, ty) => (TAbbrev' (a, ty), empty)
and rdTypeSpine sp = case TypeSpine.prj sp of
	  TNil => (TNil', empty)
	| TApp (N, S) => join2 TApp' (rdObj N) (rdTypeSpine S)
and rdSyncType sty = case SyncType.prj sty of
	  TTensor (S1, S2) => join2 TTensor' (rdSyncType S1) (rdSyncType S2)
	| TOne => (TOne', empty)
	| Exists (x, A, S) =>
			joinDep STClos Exists' x (rdType A) (rdSyncType S)
		(*join2 (fn (A', S') => Exists' (x, A', S')) (rdType A) (Util.map2 decr (rdSyncType S))*)
	| Async A => Util.map1 Async' (rdType A)
and rdObj ob = case Obj.prj ob of
	  LinLam (x, N) => Util.map12 (fn N' => LinLam' (x, N')) decr (rdObj N)
	| Lam (x, N) => Util.map12 (fn N' => Lam' (x, N')) decr (rdObj N)
	| AddPair (N1, N2) => join2 AddPair' (rdObj N1) (rdObj N2)
	| Unit => (Unit', empty)
	| Monad E => Util.map1 Monad' (rdExp E)
	| Atomic (H, S) => join2 (fn (H', S') => Atomic' (H', S')) (rdHead H) (rdSpine S)
	| Redex (N, A, S) => join2 (fn (N', S') => Redex' (N', A, S')) (rdObj N) (rdSpine S)
	| Constraint (N, A) => join2 Constraint' (rdObj N) (rdType A)
and rdHead h = case h of
	  Const c => (Const c, empty)
(*			let val (impl', occs) = ListPair.unzip (map rdObj impl)
			in (Const (c, impl'), foldl union empty occs) end*)
	| Var n => (Var n, occur n)
	| UCVar v => (UCVar v, empty)
	| LogicVar (X as {ctx, s, ty, ...}) =>
			let val ctxL = length $ Context.ctx2list $ valOf $ !ctx
				val subL = Subst.fold (fn (_, n) => n+1) (fn _ => 0) s
				fun occurSubOb Undef = empty
				  | occurSubOb (Ob ob) = #2 (rdObj ob)
				  | occurSubOb (Idx n) = occur n
				val occurSub = Subst.fold (union o (Util.map1 occurSubOb))
							(fn m => occurFromTo (m+1) (ctxL-subL+m)) s
			in (LogicVar (X with'ty (#1 (rdType ty))), occurSub) end
and rdSpine sp = case Spine.prj sp of
	  Nil => (Nil', empty)
	| App (N, S) => join2 App' (rdObj N) (rdSpine S)
	| LinApp (N, S) => join2 LinApp' (rdObj N) (rdSpine S)
	| ProjLeft S => Util.map1 ProjLeft' (rdSpine S)
	| ProjRight S => Util.map1 ProjRight' (rdSpine S)
and rdExp e = case ExpObj.prj e of
	  Let (p, N, E) =>
			join2 (fn (p', (N', E')) => Let' (p', N', E')) (rdPattern p)
				(join2 (fn x => x) (rdObj N) (Util.map2 (decrn (nbinds p)) (rdExp E)))
	| Mon M => Util.map1 Mon' (rdMonadObj M)
and rdMonadObj m = case MonadObj.prj m of
	  Tensor (M1, M2) => join2 Tensor' (rdMonadObj M1) (rdMonadObj M2)
	| One => (One', empty)
	| DepPair (N, M) => join2 DepPair' (rdObj N) (rdMonadObj M)
	| Norm N => Util.map1 Norm' (rdObj N)
and rdPattern p = case Pattern.prj p of
	  PTensor (p1, p2) => join2 PTensor' (rdPattern p1) (rdPattern p2)
	| POne => (POne', empty)
	| PDepPair (x, A, p) =>
			join2 (fn (A', p') => PDepPair' (x, A', p')) (rdType A) (Util.map2 decr (rdPattern p))
	| PVar (x, A) => Util.map1 (fn A' => PVar' (x, A')) (rdType A)

val remDepKind = #1 o rdKind
val remDepType = #1 o rdType
val remDepObj = #1 o rdObj

end
