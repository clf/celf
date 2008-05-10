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

signature APPROXTYPES =
sig

val traceApx : bool ref

type context
val emptyCtx : context

exception ExnApxUnifyType of string

val occur : Syntax.typeLogicVar -> Syntax.apxAsyncType -> unit
val apxUnifyType : Syntax.apxAsyncType * Syntax.apxAsyncType -> unit

val apxCheckKind : context * Syntax.kind -> Syntax.kind
val apxCheckType : context * Syntax.asyncType -> Syntax.asyncType
val apxCheckTypeSpine : context * Syntax.typeSpine * Syntax.apxKind -> Syntax.typeSpine
val apxCheckSyncType : context * Syntax.syncType -> Syntax.syncType
val apxCheckObj : context * Syntax.obj * Syntax.apxAsyncType -> context * bool * Syntax.obj
val apxInferObj : context * Syntax.obj -> context * bool * Syntax.obj * Syntax.apxAsyncType
val apxInferExp : context * Syntax.expObj -> context * bool * Syntax.expObj * Syntax.apxSyncType
val apxCheckPattern : context * Syntax.pattern -> Syntax.pattern
val apxInferMonadObj : context * Syntax.monadObj -> context * bool * Syntax.monadObj * Syntax.apxSyncType

val apxCheckKindEC : Syntax.kind -> Syntax.kind
val apxCheckTypeEC : Syntax.asyncType -> Syntax.asyncType
val apxCheckObjEC : Syntax.obj * Syntax.apxAsyncType -> Syntax.obj

end
