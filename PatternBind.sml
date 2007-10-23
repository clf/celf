structure PatternBind :> PATTERNBIND =
struct

open Context
open Syntax

(* patBind : (asyncType -> 'a) -> pattern -> 'a context -> 'a context *)
fun patBind f p ctx = case Pattern.prj p of
	  PTensor (p1, p2) => patBind f (PClos (p2, Subst.shift (nbinds p1))) (patBind f p1 ctx)
	| POne => ctx
	| PDepPair (x, A, p) => patBind f p (ctxPushUN (x, f A, ctx))
	| PVar (x, A) => ctxPushLIN (x, f A, ctx)

(* patUnbind : pattern * 'a context * bool -> 'a context *)
fun patUnbind (p, ctx, t) = case Pattern.prj p of
	  PTensor (p1, p2) => patUnbind (p1, patUnbind (p2, ctx, t), t)
	| POne => ctx
	| PDepPair (x, _, p) => ctxPopUN (patUnbind (p, ctx, t))
	| PVar (x, _) => ctxPopLIN (t, ctx)

(* patUnbindOpt : pattern * 'a context * bool -> 'a context option *)
fun patUnbindOpt pCtxT = SOME (patUnbind pCtxT) handle ExnCtx _ => NONE

end
