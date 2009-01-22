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
val instantiate : Syntax.obj option VRef.vref * Syntax.obj * Syntax.constr VRef.vref list VRef.vref * word -> unit

val pruneCtx : exn -> (Syntax.asyncType -> Syntax.asyncType) -> Syntax.subst
		-> Syntax.asyncType Context.context -> Syntax.asyncType Context.context

exception ExnOccur

val objExists : Syntax.obj option VRef.vref -> Syntax.obj -> Syntax.obj option
val typeExists : Syntax.obj option VRef.vref -> Syntax.asyncType -> Syntax.asyncType option

val unify : Syntax.asyncType * Syntax.asyncType * (unit -> string) -> unit
val unifiable : Syntax.asyncType * Syntax.asyncType -> bool

end
