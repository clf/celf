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

structure ImplicitVars :> IMPLICITVARS =
struct

open Syntax
open SymbTable

type implicits = (string * asyncType) list

val ucTable = ref (empty ()) : asyncType Table ref

fun getUCTable () = !ucTable

val newint = ref 0
fun newname () = (newint := 1 + !newint; "xx" ^ Int.toString (!newint))
fun freshname () =
	let val v = newname ()
	in if isSome (peek (!ucTable, v)) then freshname () else v end

fun newUCVar ty = let val v = freshname () in ucTable := insert (!ucTable, v, ty); UCVar v end

(* resetUCTable : unit -> unit *)
fun resetUCTable () = ucTable := empty ()

(* mapUCTable : (asyncType -> asyncType) -> unit *)
fun mapUCTable f = ucTable := mapTable f (!ucTable)

(* appUCTable : (asyncType -> unit) -> unit *)
fun appUCTable f = appTable f (!ucTable)

(* noUCVars : unit -> unit *)
fun noUCVars () =
	if null (toList (!ucTable)) then ()
	else raise ExnDeclError (GeneralErr,
		"Upper-case (implicitly bound) variables are not allowed here\n")

(* apxUCLookup : string -> apxAsyncType *)
fun apxUCLookup x =
	case peek (!ucTable, x) of
		  NONE => let val A = newTVar() in ucTable := insert (!ucTable, x, A); asyncTypeToApx A end
		| SOME A => asyncTypeToApx A

(* ucLookup : string -> asyncType *)
fun ucLookup x = valOf (peek (!ucTable, x))

(* sort : unit -> implicits *)
fun sort () =
	let fun getUCvars ty =
			let val ucs = ref []
				fun collect t = Util.objAppType
							(fn Atomic (UCVar x, ()) => ucs := x::(!ucs)
							  | Atomic (LogicVar {ty, s, ...}, ()) =>
									collect (TClos (ty, s))
							  | _ => ()) t
				val () = collect ty
			in !ucs end
		fun listToSet l = foldl (fn (x, s) => insert (s, x, ())) (empty ()) l
		val ucVars = toList (!ucTable)
		val graph = foldl
				(fn ((x, _), g) => insert (g, x, (ref (empty ()), ref (empty ()))))
				(empty ()) ucVars
		fun outs x = #2 (valOf (peek (graph, x)))
		fun ins x = #1 (valOf (peek (graph, x)))
		val () = List.app
				(fn (x, A) =>
					let val dependencies = getUCvars A
						val xIn = ins x
						val () = xIn := listToSet dependencies
						val () = List.app
								(fn y =>
									let val yOut = outs y
									in yOut := insert (!yOut, x, ()) end)
								dependencies
					in () end)
				ucVars
		val noIns = map #1 (List.filter
								(fn (_, (ref inset, _)) => 0 = numItems inset)
								(toList graph))
		fun topsort l [] =
				if length l = length ucVars then rev l
				else raise ExnDeclError (TypeErr,
					"Circular dependencies between implicit variables")
		  | topsort l (x::xs) =
				topsort ((x, ucLookup x)::l)
					(xs @ foldl
						(fn ((y, ()), xs) =>
							let val yIn = ins y
								val () = yIn := delete (!yIn, x)
							in if numItems (!yIn) = 0 then y::xs else xs end)
						[] ((toList o ! o outs) x))
	in topsort [] noIns end

end
