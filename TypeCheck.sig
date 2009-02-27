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

signature TYPECHECK =
sig

(* Page 9: of CLF TR CMU-CS-02-101 *)

type context

val enable : unit -> unit
val isEnabled : unit -> bool

val checkKind : context * Syntax.nfKind -> unit
val checkType : context * Syntax.nfAsyncType -> unit
val checkTypeSpine : context * Syntax.nfTypeSpine * Syntax.nfKind -> unit
val checkSyncType : context * Syntax.nfSyncType -> unit
val checkObj : context * Syntax.nfObj * Syntax.nfAsyncType -> context
val inferSpine : context * Syntax.nfSpine * Syntax.nfAsyncType -> context * Syntax.nfAsyncType
val inferHead : context * Syntax.nfHead -> context * Syntax.nfAsyncType

val checkKindEC : Syntax.kind -> unit
val checkTypeEC : Syntax.asyncType -> unit
val checkObjEC : Syntax.obj * Syntax.asyncType -> unit

end
