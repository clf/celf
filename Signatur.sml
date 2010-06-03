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

signature TLU_Signatur = TOP_LEVEL_UTIL
functor SignaturFun (Syn : SYNTAX_CORE1) =
struct

structure Syn = Syn
open Syn

open SymbTable

val sigTable = ref (empty()) : decl Table ref
val sigDelta = ref [] : decl list ref

fun getKiTyOpt c =
	case peek (!sigTable, c) of
		NONE => NONE
	  | SOME (ConstDecl (_, imps, kity)) => SOME (imps, kity)
	  | SOME _ => raise Fail "Internal error: getKiTy called on abbrev\n"

fun getKiTy c = case getKiTyOpt c of
	  NONE => raise Fail ("Undeclared identifier: "^c^"\n")
	| SOME x => x

fun getType c = case getKiTy c of
	  (imps, Ty ty) => (imps, ty)
	| (_, Ki _) => raise Fail ("Type "^c^" is used as an object\n")

fun getKind a = case getKiTy a of
	  (_, Ty _) => raise Fail ("Object "^a^" is used as a type\n")
	| (imps, Ki ki) => (imps, ki)

(* newImplicits implicits -> obj list *)
(*fun newImplicits imps = map (fn (_, A) => newLVar A) imps*)

(* newTSpine : kind -> typeSpine *)
(*fun newTSpine ki = case Kind.prj ki of
	  Type => TNil'
	| KPi (_, A, K) => TApp' (newLVar A, newTSpine K)*)

fun idFromDecl (ConstDecl (s, _, _)) = s
  | idFromDecl (TypeAbbrev (s, _)) = s
  | idFromDecl (ObjAbbrev (s, _, _)) = s
  | idFromDecl (Query _) = raise Fail "Internal error: Adding query to sig table\n"

fun declSetId id (ConstDecl (_, imps, kity)) = ConstDecl (id, imps, kity)
  | declSetId id (TypeAbbrev (_, ty)) = TypeAbbrev (id, ty)
  | declSetId id (ObjAbbrev (_, ty, ob)) = ObjAbbrev (id, ty, ob)
  | declSetId id (Query _) = raise Fail "Internal error: Adding query to sig table\n"

(******************)

(* getSigDelta : unit -> decl list *)
fun getSigDelta () = rev (!sigDelta) before sigDelta := []

(* sigAddDecl : decl -> unit *)
fun sigAddDecl dec =
	let val id = idFromDecl dec
		val allowDup = String.sub (id, 0) = #"-"
		fun checkId x = not $ isSome $ peek (!sigTable, x)
		fun nextId x n =
			let val x' = x ^ Int.toString n
			in if checkId x' then x' else nextId x (n+1) end
		val id' =
			if checkId id then id
			else if allowDup then nextId id 1
			else raise Fail ("Error name clash: " ^ id)
		val dec' = declSetId id' dec
	in ( sigTable := insert (!sigTable, id', dec')
	   ; sigDelta := dec' :: !sigDelta )
	end

(* getImplLength : string -> int *)
fun getImplLength c = case getKiTyOpt c of NONE => 0 | SOME (imps, _) => imps

(* sigLookupKind : string -> kind *)
fun sigLookupKind a = #2 (getKind a)
	(*let val (imps, ki) = getKind a
		(*fun im2ki [] = ki
		  | im2ki ((x, A)::im) = KPi' (x, A, im2ki im)*)
	in foldr (fn ((x, A), im) => KPi' (SOME x, A, im)) ki imps end*)

(* sigLookupType : string -> asyncType *)
fun sigLookupType a = #2 (getType a)
	(*let val (imps, ty) = getType a
	in foldr (fn ((x, A), im) => TPi' (SOME x, A, im)) ty imps end*)

(* sigLookupApxKind : string -> apxKind *)
(*fun sigLookupApxKind a = #2 (getKind a)*)

(* sigLookupApxType : string -> apxAsyncType *)
(*fun sigLookupApxType c = #2 (getType c)*)

(* sigNewImplicitsType : string -> obj list *)
(*fun sigNewImplicitsType a = newImplicits (#1 (getKind a))*)

(* sigNewImplicitsObj : string -> obj list *)
(*fun sigNewImplicitsObj a = newImplicits (#1 (getType a))*)

(* sigNewTAtomic : string -> asyncType *)
(*fun sigNewTAtomic a =
	let val (imps, ki) = getKind a
	in TAtomic' (a, foldr TApp' (newTSpine ki) (newImplicits imps)) end*)

(* sigGetTypeAbbrev : string -> asyncType option *)
fun sigGetTypeAbbrev a =
	case peek (!sigTable, a) of
		NONE => raise Fail ("Undeclared identifier: "^a^"\n")
	  | SOME (TypeAbbrev (_, ty)) => SOME ty
	  | SOME (ObjAbbrev _) => raise Fail ("Object "^a^" is used as a type\n")
	  | SOME (ConstDecl _) => NONE
	  | SOME (Query _) => raise Fail "Internal error: sigGetTypeAbbrev"

(* sigGetObjAbbrev : string -> (obj * asyncType) option *)
fun sigGetObjAbbrev c =
	case peek (!sigTable, c) of
		NONE => raise Fail ("Undeclared identifier: "^c^"\n")
	  | SOME (ObjAbbrev (_, ty, ob)) => SOME (ob, ty)
	  | SOME (TypeAbbrev _) => raise Fail ("Type "^c^" is used as an object\n")
	  | SOME (ConstDecl _) => NONE
	  | SOME (Query _) => raise Fail "Internal error: sigGetObjAbbrev"

end
