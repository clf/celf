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

signature ETA =
sig

val traceEta : bool ref

type context

val etaContract : exn -> Syntax.nfObj -> Context.mode * int
val etaContractLetMon : Syntax.nfExpObj -> (Syntax.nfHead * Syntax.nfSpine) option

val etaExpand : (unit -> string) -> Syntax.apxAsyncType * Syntax.head * Syntax.spine -> Syntax.obj
val etaExpandKind : context * Syntax.kind -> Syntax.kind
val etaExpandType : context * Syntax.asyncType -> Syntax.asyncType
val etaExpandTypeSpine : context * Syntax.typeSpine * Syntax.apxKind -> Syntax.typeSpine
val etaExpandSyncType : context * Syntax.syncType -> Syntax.syncType
val etaExpandObj : context * Syntax.obj * Syntax.apxAsyncType -> Syntax.obj
val etaExpandHead : context * Syntax.head -> Syntax.head * Syntax.apxAsyncType
val etaExpandSpine : (unit -> string) -> context * Syntax.spine * Syntax.apxAsyncType
		-> Syntax.spine * Syntax.apxAsyncType
val etaExpandExp : context * Syntax.expObj * Syntax.apxSyncType -> Syntax.expObj
val etaExpandMonadObj : context * Syntax.monadObj * Syntax.apxSyncType -> Syntax.monadObj

val etaExpandKindEC : Syntax.kind -> Syntax.kind
val etaExpandTypeEC : Syntax.asyncType -> Syntax.asyncType
val etaExpandObjEC : Syntax.obj * Syntax.apxAsyncType -> Syntax.obj

end
