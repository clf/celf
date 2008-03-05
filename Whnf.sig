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

signature WHNF =
sig

structure Syn : SYNTAX_CORE2
val whnfObj : Syn.obj -> (Syn.spine, Syn.expObj, Syn.obj) Syn.nfObjFF
val whnfExp : Syn.expObj ->
	(Syn.head * Syn.spine, Syn.monadObj, Syn.pattern, Syn.expObj) Syn.expObjFF

val appendSpine : Syn.spine * Syn.spine -> Syn.spine

(*
val whnfLetSpine : Syntax.expObj -> Syntax.expObj

val normalizeKind : Syntax.kind -> Syntax.kind
val normalizeType : Syntax.asyncType -> Syntax.asyncType
val normalizeObj : Syntax.obj -> Syntax.obj
*)

end
