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

signature TLU_SignaturTable = TOP_LEVEL_UTIL
structure SignaturTable :> SIGNATUR_TABLE =
struct

open Syntax
open SymbTable

datatype lr = L | R
datatype headType = HdMonad | HdAtom of string

val candMonad = ref [] : (string * lr list * asyncType) list ref

val candAtom = ref (empty ()) : (string * lr list * asyncType) list Table ref

fun resetCands () =
	( candMonad := []
	; candAtom := empty () )

fun lookupAtom a = getOpt (peek (!candAtom, a), [])

fun pushAtom a x = candAtom := insert (!candAtom, a, x :: lookupAtom a)

(* heads : asyncType -> (lr list * headType) list *)
fun heads ty = case Util.typePrjAbbrev ty of
	  TLPi (_, _, A) => heads A
	| AddProd (A, B) => map (map1 (fn lrs => L::lrs)) (heads A)
						@ map (map1 (fn lrs => R::lrs)) (heads B)
	| TMonad _ => [([], HdMonad)]
	| TAtomic (a, _) => [([], HdAtom a)]
	| _ => raise Fail "Internal error: heads: TAbbrev"

fun updDecl (ConstDecl (c, _, Ty ty)) =
		let val hds = heads ty
		in app (fn (lrs, HdMonad) => candMonad := (c, lrs, ty) :: !candMonad
				 | (lrs, HdAtom a) => pushAtom a (c, lrs, ty)) hds
		end
  | updDecl _ = ()

fun update () = app updDecl (Signatur.getSigDelta ())

(* getCandMonad : unit -> (string * lr list * asyncType) list *)
fun getCandMonad () = ( update () ; !candMonad )

(* getCandAtomic : string -> (string * lr list * asyncType) list *)
fun getCandAtomic a = ( update () ; lookupAtom a )

end
