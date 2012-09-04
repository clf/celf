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

signature OPSEMCTX =
sig

exception ExnCtx of string

(* NONE means used; we never need to distinguish used affine and used linear *)
type 'a context

val ctx2list : 'a context -> (string * 'a option * Context.cmodality) list

val emptyCtx : unit -> 'a context

val findNonDep : (int * string * 'a * Context.modality -> bool) -> 'a context
                 -> (int * string * 'a * Context.modality) option

val ctxIntPart : 'a context -> 'a context
val ctxAffPart : 'a context -> 'a context

(* val ctxLookupNum : 'a context * int -> 'a context * Context.modality * 'a *)
val removeHyp : 'a context * int * Context.modality -> 'a context

val ctxPush : string option * Context.modality * 'a * 'a context -> 'a context

(* New functions for sparse contexts *)

(* ctxPushList is the list version of ctxPush.
   Elements are pushed left-to-right
 *)
val ctxPushList : (string option * Context.modality * 'a) list -> 'a context -> 'a context

(* ctxPopNum n repeats ctxPop n times *)
val ctxPopNum : int -> 'a context -> 'a context

val nonDepPart : 'a context -> int * (int * (string * 'a * Context.modality)) list

val affIntersect : 'a context * 'a context -> 'a context
val linearDiff : 'a context * 'a context -> 'a context
val nolin : 'a context -> bool

val linearIndices : 'a context -> int list

end
