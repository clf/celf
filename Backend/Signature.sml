signature TLU_Signature = TOP_LEVEL_UTIL

structure Signature :> SIGNATURE =
struct

open SymbTable
open InternalSyntax

val modeTable = ref (empty()) : modeDecl Table ref
val posAtomsTable = ref (empty()) : unit Table ref
val sigTable = ref (empty()) : decl Table ref
val sigOrdered = ref [] : decl list ref

val monadicCand = ref [] : (string * lr list * asyncType) list ref
val atomicCand = ref (empty ()) : (string * lr list * asyncType) list Table ref


fun tableInsert (t, id, v) = ( t := insert (!t, id, v) )
fun tableDelete (t, id) = case peek (!t, id) of
                              NONE => ()
                            | SOME _ => ( t := delete (!t, id) )

(* NO error checking (duplicate names, arg outside domain of partial functions)
 * since these have been checked already in Signatur.sml.
 * If Signatur.sml is removed, error checking should be done here *)

fun getSignature () = rev (!sigOrdered)

(* getAtomicCand : string -> (string * lr list * asyncType) list *)
fun getAtomicCand a = getOpt (peek (!atomicCand, a), [])

fun insertAtomicCand a x =
    atomicCand := insert (!atomicCand, a, x :: getAtomicCand a)

fun updateCand c ty =
    let
      val hds = heads ty
      fun upd (lrs, HdMonad) = ( monadicCand := (c, lrs, ty) :: !monadicCand )
        | upd (lrs, HdAtom a) = ( insertAtomicCand a (c, lrs, ty)
                                ; tableDelete (posAtomsTable, a) )
    in
      app upd hds
    end

(* getMonadicCand : unit -> (string * lr list * asyncType) list *)
fun getMonadicCand () = !monadicCand

(* getModeDecl : string -> modeDecl option *)
fun getModeDecl id = peek (!modeTable, id)


fun insertDecl d =
    let
      fun insertD (d as ConstDecl (id,_,Ty ty)) =
          ( tableInsert (sigTable, id, d)
          ; updateCand id ty )
        | insertD (d as ConstDecl (id,_,Ki _)) =
          ( tableInsert (sigTable, id, d)
          ; tableInsert (posAtomsTable, id, ()) )
        | insertD (d as TypeAbbrev (id,_)) = tableInsert (sigTable, id, d)
        | insertD (d as ObjAbbrev (id,_,_)) = tableInsert (sigTable, id, d)
        | insertD (d as Query _) = ()
        | insertD (d as Trace _) = ()
        | insertD (d as Exec _) = ()
        | insertD (d as Mode (id,implmd,md)) =
          let
            val allmd = getOpt (implmd, []) @ md
          in
            tableInsert (modeTable, id, allmd)
          end
        | insertD (d as Empty id) = tableInsert (posAtomsTable, id, ())
    in
      insertD d
    ; sigOrdered := d :: !sigOrdered
    end


(* isPosAtom : string -> bool *)
fun isPosAtom id = isSome (peek (!posAtomsTable, id))

(* getImplicitNum : string -> int *)
fun getImplicitNum c =
    case peek (!sigTable, c) of
        NONE => 0
      | SOME (ConstDecl (_, imps, kity)) => imps
      | SOME _ => raise Fail "Internal error: Signature.getImplLength"

end
