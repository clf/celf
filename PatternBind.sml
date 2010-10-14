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

fun pBindAdd add push (p, sty) ctx = case (Pattern.prj p, SyncType.prj sty) of
	  (PDepTensor (p1, p2), LExists (p1', S1, S2)) =>
			pBindAdd add push (p2, S2) (pBindAdd add push (add (p1, p1'), S1) ctx)
	| (POne, TOne) => ctx
	| (PDown x, TDown A) => push (PDown x, A, ctx)
	| (PAffi x, TAffi A) => push (PAffi x, A, ctx)
	| (PBang x, TBang A) => push (PBang x, A, ctx)
	| _ => raise Fail "Internal error: patternBind"
fun pBindApx push (p, sty) ctx = case (Pattern.prj p, ApxSyncType.prj sty) of
	  (PDepTensor (p1, p2), ApxTTensor (S1, S2)) =>
			pBindApx push (p2, S2) (pBindApx push (p1, S1) ctx)
	| (POne, ApxTOne) => ctx
	| (PDown x, ApxTDown A) => push (PDown x, A, ctx)
	| (PAffi x, ApxTAffi A) => push (PAffi x, A, ctx)
	| (PBang x, ApxTBang A) => push (PBang x, A, ctx)
	| _ => raise Fail "Internal error: patternBind"
fun pBind push = pBindAdd (fn (p1, _) => p1) push

fun tpush f (PDown (), A, ctx) = ctxPushNO (f A, ctx)
  | tpush f (PAffi (), A, ctx) = ctxPushNO (f A, ctx)
  | tpush f (PBang NONE, A, ctx) = ctxPushNO (f A, ctx)
  | tpush f (PBang (SOME x), A, ctx) = ctxPush (x, INT, f A, ctx)
  | tpush f _ = raise Fail "Internal error: tpush"
fun opush f (PDown x, A, ctx) = ctxPush (x, LIN, f A, ctx)
  | opush f (PAffi x, A, ctx) = ctxPush (x, AFF, f A, ctx)
  | opush f (PBang x, A, ctx) = ctxPush (x, INT, f A, ctx)
  | opush f _ = raise Fail "Internal error: opush"
fun depPush {dep, nodep} (PDown (), A, ctx) = ctxPush ("", LIN, nodep A, ctx)
  | depPush {dep, nodep} (PAffi (), A, ctx) = ctxPush ("", AFF, nodep A, ctx)
  | depPush {dep, nodep} (PBang NONE, A, ctx) = ctxPush ("", INT, nodep A, ctx)
  | depPush {dep, nodep} (PBang (SOME x), A, ctx) = ctxPush (x, INT, dep A, ctx)
  | depPush _ _ = raise Fail "Internal error: otpush"

val tpatBind = pBind (tpush (fn x=>x))
val opatBind = pBind (opush (fn x=>x))
val tpatBindApx = pBindApx (tpush (fn x=>x))
val opatBindApx = pBindApx (opush (fn x=>x))
fun tpatBindNf (p, sty) ctx = pBind (tpush normalizeType) (p, unnormalizeSyncType sty) ctx
fun opatBindNf (p, sty) ctx = pBind (opush normalizeType) (p, unnormalizeSyncType sty) ctx
fun depPatBind fs (p, sty) ctx = pBindAdd Util.patternAddDep (depPush fs) (p, sty) ctx

(* patUnbind : opattern * 'a context -> 'a context *)
fun patUnbind (p, ctx) = case Pattern.prj p of
	  PDepTensor (p1, p2) => patUnbind (p1, patUnbind (p2, ctx))
	| POne => ctx
	| PDown x => ctxPop ctx
	| PAffi x => ctxPop ctx
	| PBang x => ctxPop ctx

end
