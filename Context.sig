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

signature CONTEXT =
sig

exception ExnCtx of string

datatype mode = INT | LIN
type cmode = mode option
type 'a context

val ctx2list : 'a context -> (string * 'a * cmode) list
val ctxCons : (string * 'a * cmode) -> 'a context -> 'a context
val ctxMap : ('a -> 'b) -> 'a context -> 'b context

val emptyCtx : 'a context

val ctxDelLin : 'a context -> 'a context

val ctxLookupNum : 'a context * int -> 'a context * mode * 'a
val ctxLookupName : 'a context * string -> (int * mode * 'a * 'a context) option

val ctxPushINT : string * 'a * 'a context -> 'a context
val ctxCondPushINT : string option * 'a * 'a context -> 'a context
val ctxPushLIN : string * 'a * 'a context -> 'a context
val ctxPopINT : 'a context -> 'a context
val ctxPopLIN : bool * 'a context -> 'a context
val ctxPopLINopt : bool * 'a context -> 'a context option

val ctxAddJoin : bool * bool -> 'a context * 'a context -> 'a context
val ctxAddJoinOpt : bool * bool -> 'a context * 'a context -> 'a context option

end
