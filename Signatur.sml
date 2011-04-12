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

fun resetSig () =
	( sigTable := empty ()
	; sigDelta := [] )

fun getKiTyOpt c =
	case peek (!sigTable, c) of
		NONE => NONE
	  | SOME (ConstDecl (_, imps, kity)) => SOME (imps, kity)
	  | SOME _ => raise Fail "Internal error: getKiTy called on abbrev"

fun getKiTy c = case getKiTyOpt c of
	  NONE => raise ExnDeclError (UndeclId, c)
	| SOME x => x

fun getType c = case getKiTy c of
	  (imps, Ty ty) => (imps, ty)
	| (_, Ki _) => raise ExnDeclError (KindErr, "Type "^c^" is used as an object\n")

fun getKind a = case getKiTy a of
	  (_, Ty _) => raise ExnDeclError (KindErr, "Object "^a^" is used as a type\n")
	| (imps, Ki ki) => (imps, ki)

fun idFromDecl (ConstDecl (s, _, _)) = s
  | idFromDecl (TypeAbbrev (s, _)) = s
  | idFromDecl (ObjAbbrev (s, _, _)) = s
  | idFromDecl (Query _) = raise Fail "Internal error: Adding query to sig table"

fun declSetId id (ConstDecl (_, imps, kity)) = ConstDecl (id, imps, kity)
  | declSetId id (TypeAbbrev (_, ty)) = TypeAbbrev (id, ty)
  | declSetId id (ObjAbbrev (_, ty, ob)) = ObjAbbrev (id, ty, ob)
  | declSetId id (Query _) = raise Fail "Internal error: Adding query to sig table"

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
			else raise ExnDeclError (GeneralErr, "Identifier is already defined\n")
		val dec' = declSetId id' dec
	in ( sigTable := insert (!sigTable, id', dec')
	   ; sigDelta := dec' :: !sigDelta )
	end

(* getImplLength : string -> int *)
fun getImplLength c = case getKiTyOpt c of NONE => 0 | SOME (imps, _) => imps

(* sigLookupKind : string -> kind *)
fun sigLookupKind a = #2 (getKind a)

(* sigLookupType : string -> asyncType *)
fun sigLookupType a = #2 (getType a)

(* sigGetTypeAbbrev : string -> asyncType option *)
fun sigGetTypeAbbrev a =
	case peek (!sigTable, a) of
		NONE => raise ExnDeclError (UndeclId, a)
	  | SOME (TypeAbbrev (_, ty)) => SOME ty
	  | SOME (ObjAbbrev _) => raise ExnDeclError (KindErr, "Object "^a^" is used as a type\n")
	  | SOME (ConstDecl _) => NONE
	  | SOME (Query _) => raise Fail "Internal error: sigGetTypeAbbrev"

(* sigGetObjAbbrev : string -> (obj * asyncType) option *)
fun sigGetObjAbbrev c =
	case peek (!sigTable, c) of
		NONE => raise ExnDeclError (UndeclId, c)
	  | SOME (ObjAbbrev (_, ty, ob)) => SOME (ob, ty)
	  | SOME (TypeAbbrev _) => raise ExnDeclError (KindErr, "Type "^c^" is used as an object\n")
	  | SOME (ConstDecl _) => NONE
	  | SOME (Query _) => raise Fail "Internal error: sigGetObjAbbrev"

end
