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

signature UNIFY =
sig

val outputUnify : bool ref

exception ExnUnify of string

val resetConstrs : unit -> unit
val noConstrs : unit -> unit
val addConstraint : Syntax.constr VRef.vref * Syntax.constr VRef.vref list VRef.vref list -> unit
val instantiate : Syntax.nfObj option VRef.vref * Syntax.nfObj * Syntax.constr VRef.vref list VRef.vref * word -> unit

val pruneCtx : exn -> (Syntax.nfAsyncType -> Syntax.nfAsyncType) -> Syntax.subst
		-> Syntax.nfAsyncType Context.context -> Syntax.nfAsyncType Context.context
val pruneLVar : Syntax.nfHead -> unit

exception ExnOccur

val objExists : Syntax.nfObj option VRef.vref -> Syntax.nfObj -> Syntax.nfObj option
val typeExists : Syntax.nfAsyncType -> Syntax.nfAsyncType option

val unify : Syntax.asyncType * Syntax.asyncType * (unit -> string) -> unit
val unifiable : Syntax.asyncType * Syntax.asyncType -> bool

end
