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

signature EXACTTYPES =
sig

val traceExact : bool ref

type context
val emptyCtx : context

val checkKind : context * Syntax.kind -> unit
val checkType : context * Syntax.asyncType -> unit
val checkTypeSpine : (unit -> string) -> context * Syntax.typeSpine * Syntax.kind -> unit
val checkSyncType : context * Syntax.syncType -> unit
val checkObj : context * Syntax.obj * Syntax.asyncType -> context
val inferHead : context * Syntax.head -> context * Syntax.asyncType
val inferSpine : context * Syntax.spine * Syntax.asyncType -> context * Syntax.asyncType
val checkExp : context * Syntax.expObj * Syntax.syncType -> context
val checkMonadObj : context * Syntax.monadObj * Syntax.syncType -> context

val checkKindEC : Syntax.kind -> unit
val checkTypeEC : Syntax.asyncType -> unit
val checkObjEC : Syntax.obj * Syntax.asyncType -> unit

end
