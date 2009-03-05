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

signature TLU_Parse = TOP_LEVEL_UTIL
structure Parse :> PARSE =
struct

open Syntax

datatype unifiedType = Pos of syncType | Neg of asyncType

fun unif2async (Neg A) = A
  | unif2async (Pos _) = raise Fail "Parse error: AsyncType expected"
fun unif2sync (Neg A) = TDown' A
  | unif2sync (Pos S) = S
val u2a = unif2async
val u2s = unif2sync

fun syncType2tpatNoDep s =
	let fun s2p S = case SyncType.prj S of LExists (_, S1, S2) => PDepTensor (S1, S2)
			| TOne => POne | TDown _ => PDown () | TAffi _ => PAffi () | TBang _ => PBang NONE
	in TPatternRec.unfold s2p s end
fun lolli (S, B) =
	let val S' = u2s S
	in Neg $ TLPi' (syncType2tpatNoDep S', S', u2a B) end
fun affLolli (A, B) = Neg $ TLPi' (PAffi' (), TAffi' $ u2a A, u2a B)
fun arrow (A, B) = Neg $ TLPi' (PBang' NONE, TBang' $ u2a A, u2a B)
fun addProd (A, B) = Neg $ AddProd' (u2a A, u2a B)
fun tPi (x, A, B) = Neg $ TLPi' (PBang' $ SOME x, TBang' $ u2a A, u2a B)
fun tPi' (x, B) = Neg $ TLPi' (PBang' $ SOME x, TBang' $ newTVar (), u2a B)
fun tLPi (p, S, B) = Neg $ TLPi' (p, u2s S, u2a B)
fun monad A = Neg $ TMonad' $ u2s A
fun tensor (S1, S2) =
	let val S1' = u2s S1
	in Pos $ LExists' (syncType2tpatNoDep S1', S1', u2s S2) end
val one = Pos TOne'
fun exists (x, A, B) = Pos $ LExists' (PBang' $ SOME x, TBang' $ u2a A, u2s B)
fun exists' (x, B) = Pos $ LExists' (PBang' $ SOME x, TBang' $ newTVar (), u2s B)
fun lexists (p, S, B) = Pos $ LExists' (p, u2s S, u2s B)
fun aff A = Pos $ TAffi' $ unif2async A
fun bang A = Pos $ TBang' $ unif2async A

fun app (ob, mob) = Redex' (ob, newApxTVar (), LApp' (mob, Nil'))
fun projLeft ob = Redex' (ob, newApxTVar (), ProjLeft' Nil')
fun projRight ob = Redex' (ob, newApxTVar (), ProjRight' Nil')
fun blank () = newLVar (newTVar ())
fun headToObj h = Atomic' (h, Nil')

fun lamConstr (p, S, N) = Constraint' (LLam' (p, N), TLPi' (Util.patternO2T p, u2s S, newTVar ()))

fun letredex (p, N, E) = LetRedex' (p, Util.pat2apxSyncType p, N, E)

end
