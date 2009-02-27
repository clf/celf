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

signature PARSE =
sig

datatype unifiedType = Pos of Syntax.syncType | Neg of Syntax.asyncType

val unif2async : unifiedType -> Syntax.asyncType
val unif2sync : unifiedType -> Syntax.syncType

val lolli : unifiedType * unifiedType -> unifiedType
val affLolli : unifiedType * unifiedType -> unifiedType
val arrow : unifiedType * unifiedType -> unifiedType
val addProd : unifiedType * unifiedType -> unifiedType
val tPi : string * unifiedType * unifiedType -> unifiedType
val tPi' : string * unifiedType -> unifiedType
val tLPi : Syntax.tpattern * unifiedType * unifiedType -> unifiedType
val monad : unifiedType -> unifiedType
val tensor : unifiedType * unifiedType -> unifiedType
val one : unifiedType
val exists : string * unifiedType * unifiedType -> unifiedType
val exists' : string * unifiedType -> unifiedType
val lexists : Syntax.tpattern * unifiedType * unifiedType -> unifiedType
val aff : unifiedType -> unifiedType
val bang : unifiedType -> unifiedType

val app : Syntax.obj * Syntax.monadObj -> Syntax.obj
val projLeft : Syntax.obj -> Syntax.obj
val projRight : Syntax.obj -> Syntax.obj
val blank : unit -> Syntax.obj
val headToObj : Syntax.head -> Syntax.obj

val lamConstr : Syntax.opattern * unifiedType * Syntax.obj -> Syntax.obj
val letredex : Syntax.opattern * Syntax.obj * Syntax.expObj -> Syntax.expObj

end
