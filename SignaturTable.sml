structure SignaturTable :> SIGNATUR_TABLE =
struct

open Syntax
open SymbTable

datatype lr = L | R
datatype headType = HdMonad | HdAtom of string

val candMonad = ref [] : (string * lr list * asyncType) list ref

val candAtom = ref (empty ()) : (string * lr list * asyncType) list Table ref

fun lookupAtom a = getOpt (peek (!candAtom, a), [])

fun pushAtom a x = candAtom := insert (!candAtom, a, x :: lookupAtom a)

(* heads : asyncType -> (lr list * headType) list *)
fun heads ty = case Util.typePrjAbbrev ty of
	  Lolli (_, A) => heads A
	| TPi (_, _, A) => heads A
	| AddProd (A, B) => map (Util.map1 (fn lrs => L::lrs)) (heads A)
						@ map (Util.map1 (fn lrs => R::lrs)) (heads B)
	| Top => []
	| TMonad _ => [([], HdMonad)]
	| TAtomic (a, _) => [([], HdAtom a)]
	| _ => raise Fail "Internal error heads: TAbbrev\n"

fun updDecl (ConstDecl (c, imps, Ty ty)) =
		let val ty = foldr (fn ((x, A), im) => TPi' (x, A, im)) ty imps
			val hds = heads ty
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
