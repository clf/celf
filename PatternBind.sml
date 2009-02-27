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

structure PatternBind :> PATTERNBIND =
struct

open Context
open Syntax

(* patBind : (asyncType -> 'a) -> pattern * syncType -> 'a context -> 'a context *)
(* Invariant:  ctx |- sty : Type *)
fun tpatBind f (p, sty) ctx = case (Pattern.prj p, SyncType.prj sty) of
	  (PDepTensor (p1, p2), LExists (_, S1, S2)) => tpatBind f (p2, S2) (tpatBind f (p1, S1) ctx)
	| (POne, TOne) => ctx
	| (PDown (), TDown A) => ctxPushNO (f A, ctx)
	| (PAffi (), TAffi A) => ctxPushNO (f A, ctx)
	| (PBang NONE, TBang A) => ctxPushNO (f A, ctx)
	| (PBang (SOME x), TBang A) => ctxPush (x, INT, f A, ctx)
	| _ => raise Fail "Internal error: patternBind\n"
fun opatBind f (p, sty) ctx = case (Pattern.prj p, SyncType.prj sty) of
	  (PDepTensor (p1, p2), LExists (_, S1, S2)) => opatBind f (p2, S2) (opatBind f (p1, S1) ctx)
	| (POne, TOne) => ctx
	| (PDown x, TDown A) => ctxPush (x, LIN, f A, ctx)
	| (PAffi x, TAffi A) => ctxPush (x, AFF, f A, ctx)
	| (PBang x, TBang A) => ctxPush (x, INT, f A, ctx)
	| _ => raise Fail "Internal error: patternBind\n"

(* patBindApx : pattern * apxSyncType -> apxAsyncType context -> apxAsyncType context *)
fun tpatBindApx (p, sty) ctx = case (Pattern.prj p, ApxSyncType.prj sty) of
	  (PDepTensor (p1, p2), ApxTTensor (S1, S2)) => tpatBindApx (p2, S2) (tpatBindApx (p1, S1) ctx)
	| (POne, ApxTOne) => ctx
	| (PDown (), ApxTDown A) => ctxPushNO (A, ctx)
	| (PAffi (), ApxTAffi A) => ctxPushNO (A, ctx)
	| (PBang NONE, ApxTBang A) => ctxPushNO (A, ctx)
	| (PBang (SOME x), ApxTBang A) => ctxPush (x, INT, A, ctx)
	| _ => raise Fail "Internal error: patternBind\n"
fun opatBindApx (p, sty) ctx = case (Pattern.prj p, ApxSyncType.prj sty) of
	  (PDepTensor (p1, p2), ApxTTensor (S1, S2)) => opatBindApx (p2, S2) (opatBindApx (p1, S1) ctx)
	| (POne, ApxTOne) => ctx
	| (PDown x, ApxTDown A) => ctxPush (x, LIN, A, ctx)
	| (PAffi x, ApxTAffi A) => ctxPush (x, AFF, A, ctx)
	| (PBang x, ApxTBang A) => ctxPush (x, INT, A, ctx)
	| _ => raise Fail "Internal error: patternBind\n"

fun tpatBindNf (p, sty) ctx = tpatBind normalizeType (p, unnormalizeSyncType sty) ctx
fun opatBindNf (p, sty) ctx = opatBind normalizeType (p, unnormalizeSyncType sty) ctx

(* patUnbind : opattern * 'a context -> 'a context *)
fun patUnbind (p, ctx) = case Pattern.prj p of
	  PDepTensor (p1, p2) => patUnbind (p1, patUnbind (p2, ctx))
	| POne => ctx
	| PDown x => ctxPop ctx
	| PAffi x => ctxPop ctx
	| PBang x => ctxPop ctx

(* patUnbindOpt : opattern * 'a context -> 'a context option *)
fun patUnbindOpt pG = SOME (patUnbind pG) handle ExnCtx _ => NONE

end
