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

signature TLU_TypeRecon = TOP_LEVEL_UTIL
structure TypeRecon :> TYPERECON =
struct

open Syntax

(* mapKiTy : (kind -> kind) -> (asyncType -> asyncType) -> typeOrKind -> typeOrKind *)
fun mapKiTy fki fty (Ki ki) = Ki (fki ki)
  | mapKiTy fki fty (Ty ty) = Ty (fty ty)

(* appKiTy : (kind -> unit) -> (asyncType -> unit) -> typeOrKind -> unit *)
fun appKiTy fki fty (Ki ki) = fki ki
  | appKiTy fki fty (Ty ty) = fty ty

(* mapDecl : (kind -> kind) -> (asyncType -> asyncType) -> (obj * asyncType -> obj) -> decl -> decl *)
fun mapDecl fk ft fo (ConstDecl (id, imps, Ki ki)) = ConstDecl (id, imps, Ki (fk ki))
  | mapDecl fk ft fo (ConstDecl (id, imps, Ty ty)) = ConstDecl (id, imps, Ty (ft ty))
  | mapDecl fk ft fo (TypeAbbrev (id, ty)) = TypeAbbrev (id, ft ty)
  | mapDecl fk ft fo (ObjAbbrev (id, ty, ob)) =
		let val ty' = ft ty in ObjAbbrev (id, ty', fo (ob, ty')) end
  | mapDecl fk ft fo (Query (d, e, l, a, ty)) = Query (d, e, l, a, ft ty)

(* appDecl : (kind -> unit) -> (asyncType -> unit) -> (obj * asyncType -> unit) -> decl -> unit *)
fun appDecl fk ft fo (ConstDecl (_, _, Ki ki)) = fk ki
  | appDecl fk ft fo (ConstDecl (_, _, Ty ty)) = ft ty
  | appDecl fk ft fo (TypeAbbrev (_, ty)) = ft ty
  | appDecl fk ft fo (ObjAbbrev (_, ty, ob)) = (ft ty ; fo (ob, ty))
  | appDecl fk ft fo (Query (_, _, _, _, ty)) = ft ty

(* isQuery : decl -> bool *)
fun isQuery (Query _) = true
  | isQuery _ = false

fun declToStr (linenum, dec) =
	let val decstr = case dec of
			  ConstDecl (id, _, _) => "declaration of " ^ id
			| TypeAbbrev (id, _) => "declaration of " ^ id
			| ObjAbbrev (id, _, _) => "declaration of " ^ id
			| Query _ => "query"
	in decstr ^ " on line " ^ Int.toString linenum end

exception ExnStopCelf

(* reconstructDecl : int * decl -> unit *)
fun reconstructDecl (ldec as (_, dec)) =
		let val () = ImplicitVars.resetUCTable ()
			val dec = mapDecl ApproxTypes.apxCheckKindEC
			                  ApproxTypes.apxCheckTypeEC
			                  (ApproxTypes.apxCheckObjEC o (map2 asyncTypeToApx)) dec
			val dec = mapDecl Eta.etaExpandKindEC
			                  Eta.etaExpandTypeEC
			                  (Eta.etaExpandObjEC o (map2 asyncTypeToApx)) dec
			val () = ImplicitVars.mapUCTable Eta.etaExpandTypeEC
			val dec = mapDecl Util.removeApxKind
			                  Util.removeApxType
			                  (Util.removeApxObj o #1) dec
			val () = ImplicitVars.mapUCTable Util.removeApxType
			val () = Unify.resetConstrs ()
			val () = ImplicitVars.appUCTable ExactTypes.checkTypeEC
			val () = appDecl ExactTypes.checkKindEC
			                 ExactTypes.checkTypeEC
			                 ExactTypes.checkObjEC dec
			val () = Unify.solveLeftoverConstr ()
			val () = if isQuery dec then () else
					( appDecl ImplicitVarsConvert.logicVarsToUCVarsKind
					          ImplicitVarsConvert.logicVarsToUCVarsType
					          (ImplicitVarsConvert.logicVarsToUCVarsObj o #1) dec
					; ImplicitVars.appUCTable (Util.objAppType
						(fn Atomic (LogicVar _, _) => raise Fail "FIXME: LogicVar here???\n"
						  | _ => ())) )
			val () = ImplicitVars.mapUCTable Util.forceNormalizeType
			val dec = case dec of
				  ConstDecl (id, _, kity) =>
						let val imps = ImplicitVars.sort ()
							val imps = ImplicitVarsConvert.convUCVars2VarsImps imps
							val imps = map (map2 RemDepend.remDepType) imps
							val kity = mapKiTy (ImplicitVarsConvert.convUCVars2VarsKind imps)
							                   (ImplicitVarsConvert.convUCVars2VarsType imps) kity
							fun bindImps pi kity' =
									foldr (fn ((x, A), im) => pi (SOME x, A, im)) kity' imps
							fun tPi (sx, A, B) = TLPi' (PBang' sx, TBang' A, B)
							val kity = mapKiTy (bindImps KPi') (bindImps tPi) kity
						in ConstDecl (id, length imps, kity) end
				| TypeAbbrev _ => (ImplicitVars.noUCVars () ; dec)
				| ObjAbbrev _ => (ImplicitVars.noUCVars () ; dec)
				| Query q => Query q
			val dec = mapDecl Util.forceNormalizeKind
			                  Util.forceNormalizeType
			                  (Util.forceNormalizeObj o #1) dec
			val dec = mapDecl RemDepend.remDepKind
			                  RemDepend.remDepType
			                  (RemDepend.remDepObj o #1) dec
			val () = case dec of
				  ConstDecl (id, imps, kity) =>
							( print (id^": ")
							; appKiTy (print o PrettyPrint.printKind)
							          (print o PrettyPrint.printType) kity
							; print ".\n"
							; if TypeCheck.isEnabled () then
								appKiTy TypeCheck.checkKindEC
								        TypeCheck.checkTypeEC kity
							  else () )
				| TypeAbbrev (id, ty) =>
						( print (id^": Type = "^(PrettyPrint.printType ty)^".\n")
						; if TypeCheck.isEnabled () then TypeCheck.checkTypeEC ty else () )
				| ObjAbbrev (id, ty, ob) =>
						( print (id^": "^(PrettyPrint.printType ty)
								^" = "^(PrettyPrint.printObj ob)^".\n")
						; if TypeCheck.isEnabled () then TypeCheck.checkObjEC (ob, ty) else () )
				| Query (d, e, l, a, ty) =>
						(* d : let-depth-bound * = inf
						 * e : expected number of solutions * = ?
						 * l : number of solutions to look for * = inf
						 * a : number of times to execute the query
						 *)
						let fun n2str (SOME n) = Int.toString n
							  | n2str NONE = "*"
							val () = print ("Query ("^n2str d^", "^n2str e^", "^n2str l^", "
								^Int.toString a^") "^PrettyPrint.printType ty^".\n")
							val (ty, lvars) = ImplicitVarsConvert.convUCVars2LogicVarsType ty
							fun printInst (x, ob) = print (" #"^x^" = "^PrettyPrint.printObj ob^"\n")
							exception stopSearchExn
							val solCount = ref 0
							fun sc N = if Unify.constrsSolvable N then
								( print ("Solution: "^PrettyPrint.printObj N^"\n")
								; app printInst lvars
								; solCount := !solCount + 1
								; if TypeCheck.isEnabled () then
									TypeCheck.checkObjEC (N, ty) else ()
								; if l = SOME (!solCount) then raise stopSearchExn else () )
								else ()
							val () = OpSem.fcLimit := d
							fun runQuery 0 = false
							  | runQuery n = 
									( solCount := 0
									; if a > 1 then
										print ("Iteration "^Int.toString (a+1-n)^"\n")
									  else ()
									; OpSem.solveEC (ty, sc)
									; e = SOME (!solCount) orelse runQuery (n-1) )
						in if a = 0 orelse l = SOME 0 then
							print "Ignoring query\n"
						else if a >= 2 andalso isSome l then
							raise ExnDeclError (GeneralErr,
								"Malformed query (D,E,L,A): A>1 and L<>*\n"
								^ "Should not do simultaneous monad and backtrack exploration\n")
						else if isSome e andalso isSome l andalso valOf e >= valOf l then
							raise ExnDeclError (GeneralErr,
								"Malformed query (D,E,L,A): E>=L\n"
								^ "Uncheckable since expected number of solutions is\n"
								^ "greater than the number of solutions to look for\n")
						else if (runQuery a handle stopSearchExn => false) then
							print "Query ok.\n"
						else if isSome e then
							( print "Query failed\n"
							; raise ExnStopCelf )
						else
							()
						end
			val () = if isQuery dec then () else Signatur.sigAddDecl dec
		in () end handle
		  ExnDeclError es =>
			let val decstr = declToStr ldec
				val d = case es of
					  (UndeclId, c) => "\nUndeclared identifier \"" ^ c ^ "\" in " ^ decstr ^ "\n\n"
					| (TypeErr, s) => "\nType-checking failed in " ^ decstr ^ ":\n" ^ s ^ "\n"
					| (KindErr, s) => "\nKind-checking failed in " ^ decstr ^ ":\n" ^ s ^ "\n"
					| (AmbigType, "") => "\nAmbiguous typing in " ^ decstr ^ "\n\n"
					| (AmbigType, s) => "\nAmbiguous typing in " ^ decstr ^ ":\n" ^ s ^ "\n"
					| (GeneralErr, s) => "\nError in " ^ decstr ^ ":\n" ^ s ^ "\n"
			in print d ; raise ExnStopCelf end
		| Context.ExnCtx s =>
			( print ("\nType-checking failed in " ^ declToStr ldec ^ ":\n" ^ s ^ "\n")
			; raise ExnStopCelf )
		(*| ExnConv s =>*)


(* reconstructSignature : (int * decl) list -> unit *)
fun reconstructSignature prog = app reconstructDecl prog handle ExnStopCelf => ()


end
