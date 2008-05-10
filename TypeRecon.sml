(*  Celf
 *  Copyright (C) 2008 Anders Schack-Nielsen and Carsten Sch�rmann
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

structure TypeRecon :> TYPERECON =
struct

open Syntax

(* mapKiTy : (kind -> kind) -> (asyncType -> asyncType) -> typeOrKind -> typeOrKind *)
fun mapKiTy fki fty (Ki ki) = Ki (fki ki)
  | mapKiTy fki fty (Ty ty) = Ty (fty ty)
(* mapKiTy' : (kind -> kind) -> (asyncType -> asyncType) -> typeOrKind ref -> unit -> unit *)
(*fun mapKiTy' fki fty r = fn () => r := mapKiTy fki fty (!r)*)

(* appKiTy : (kind -> unit) -> (asyncType -> unit) -> typeOrKind -> unit *)
fun appKiTy fki fty (Ki ki) = fki ki
  | appKiTy fki fty (Ty ty) = fty ty
(* appKiTy' : (kind -> unit) -> (asyncType -> unit) -> typeOrKind ref -> unit -> unit *)
(*fun appKiTy' fki fty r = fn () => appKiTy fki fty (!r)*)

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

(* reconstructDecl : decl -> unit *)
fun reconstructDecl dec =
		let val () = ImplicitVars.resetUCTable ()
			val dec = mapDecl ApproxTypes.apxCheckKindEC
			                  ApproxTypes.apxCheckTypeEC
			                  (ApproxTypes.apxCheckObjEC o (Util.map2 asyncTypeToApx)) dec
			val dec = mapDecl Eta.etaExpandKindEC
			                  Eta.etaExpandTypeEC
			                  (Eta.etaExpandObjEC o (Util.map2 asyncTypeToApx)) dec
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
			val () = Unify.noConstrs ()
			val () = if isQuery dec then () else
					( appDecl ImplicitVars.logicVarsToUCVarsKind
					          ImplicitVars.logicVarsToUCVarsType
					          (ImplicitVars.logicVarsToUCVarsObj o Constraint') dec
					; ImplicitVars.appUCTable (Util.objAppType
						(fn Atomic (LogicVar _, _) => raise Fail "stub: LogicVar here???\n"
						  | _ => ())) )
			val () = ImplicitVars.mapUCTable Util.forceNormalizeType
			val dec = case dec of
				  ConstDecl (id, _, kity) =>
						let val imps = ImplicitVars.convUCVars2VarsImps (ImplicitVars.sort ())
							val imps = map (Util.map2 RemDepend.remDepType) imps
							val kity = mapKiTy (ImplicitVars.convUCVars2VarsKind imps)
							                   (ImplicitVars.convUCVars2VarsType imps) kity
							fun bindImps pi kity' =
									foldr (fn ((x, A), im) => pi (SOME x, A, im)) kity' imps
							val kity = mapKiTy (bindImps KPi') (bindImps TPi') kity
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
						(*let fun bindImps pi kity' =
									foldr (fn ((x, A), im) => pi (SOME x, A, im)) kity' imps
							val pkity = mapKiTy (bindImps KPi') (bindImps TPi') kity
						in*)
							( print (id^": ")
							; appKiTy (print o PrettyPrint.printKind)
							          (print o PrettyPrint.printType) kity
							; print ".\n"
							; if TypeCheck.isEnabled () then
								appKiTy TypeCheck.checkKindEC
								        TypeCheck.checkTypeEC kity
							  else () ) (*end*)
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
							val (ty, lvars) = ImplicitVars.convUCVars2LogicVarsType ty
							fun printInst (x, ob) = print (" #"^x^" = "^PrettyPrint.printObj ob^"\n")
							exception stopSearchExn
							val solCount = ref 0
							fun sc N =
								( print ("Solution: "^PrettyPrint.printObj N^"\n")
								; app printInst lvars
								; solCount := !solCount + 1
								; if l = SOME (!solCount) then raise stopSearchExn else () )
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
							(* disallow combined monad exploration and backtrack exploration *)
							raise Fail "Malformed query (D,E,L,A): A>1 and L<>*\n"
						else if isSome e andalso isSome l andalso valOf e >= valOf l then
							(* disallow querys with uncheckable expect *)
							raise Fail "Malformed query (D,E,L,A): E>=L\n"
						else if (runQuery a handle stopSearchExn => false) then
							print "Query ok.\n"
						else if isSome e then
							raise Fail "Query failed\n"
						else
							()
						end
			val () = if isQuery dec then () else Signatur.sigAddDecl dec
		in () end


(* reconstructSignature : decl list -> unit *)
fun reconstructSignature prog = app reconstructDecl prog


end
