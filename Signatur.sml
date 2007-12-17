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

(******************)

(* getSigDelta : unit -> decl list *)
fun getSigDelta () = rev (!sigDelta) before sigDelta := []

(* sigAddDecl : decl -> unit *)
fun sigAddDecl dec =
	( if isSome (peek (!sigTable, idFromDecl dec))
		then raise Fail ("Error name clash: "^idFromDecl dec)
		else ()
	; sigTable := insert (!sigTable, idFromDecl dec, dec)
	; sigDelta := dec :: !sigDelta )

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
