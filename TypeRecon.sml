structure TypeRecon :> TYPERECON =
struct

open Syntax

(* mapKiTy : (kind -> kind) -> (asyncType -> asyncType) -> typeOrKind -> typeOrKind *)
fun mapKiTy fki fty (Ki ki) = Ki (fki ki)
  | mapKiTy fki fty (Ty ty) = Ty (fty ty)

(* appKiTy : (kind -> unit) -> (asyncType -> unit) -> typeOrKind -> unit *)
fun appKiTy fki fty (Ki ki) = fki ki
  | appKiTy fki fty (Ty ty) = fty ty

(* reconstructDecl : decl -> decl *)
fun reconstructDecl (ConstDecl (id, _, kity)) =
		let val () = ImplicitVars.resetUCTable ()
			val kity = mapKiTy ApproxTypes.apxCheckKindEC
			                   ApproxTypes.apxCheckTypeEC kity
			val kity = mapKiTy Eta.etaExpandKind
			                   Eta.etaExpandType kity
			val () = ImplicitVars.mapUCTable Eta.etaExpandType
			val () = ExactTypes.resetConstrs ()
			val () = ImplicitVars.mapUCTable (fn A => (ExactTypes.checkTypeEC A; A))
			val () = appKiTy ExactTypes.checkKindEC
			                 ExactTypes.checkTypeEC kity
			val () = ExactTypes.noConstrs ()
			val () = appKiTy ImplicitVars.logicVarsToUCVarsKind
			                 ImplicitVars.logicVarsToUCVarsType kity
			val imps = ImplicitVars.convertUCVarsImps (ImplicitVars.sort ())
			val imps = map (Util.map2 PrettyPrint.remDepType) imps
			val kity = mapKiTy (ImplicitVars.convertUCVarsKind imps)
			                   (ImplicitVars.convertUCVarsType imps) kity
			val kity = mapKiTy Whnf.normalizeKind Whnf.normalizeType kity
			val kity = mapKiTy PrettyPrint.remDepKind
			                   PrettyPrint.remDepType kity
			fun bindImps pi kity' = foldr (fn ((x, A), im) => pi (x, A, im)) kity' imps
			val pkity = mapKiTy (bindImps KPi') (bindImps TPi') kity
			val () = print (id^": ")
			val () = appKiTy (print o PrettyPrint.printKind)
			                 (print o PrettyPrint.printType) pkity
			val () = print ".\n"
		in ConstDecl (id, imps, kity) end
  | reconstructDecl (TypeAbbrev (id, ty)) =
		let val () = ImplicitVars.resetUCTable ()
			val ty = ApproxTypes.apxCheckTypeEC ty
			val ty = Eta.etaExpandType ty
			val () = ImplicitVars.mapUCTable Eta.etaExpandType
			val () = ExactTypes.resetConstrs ()
			val () = ImplicitVars.mapUCTable (fn A => (ExactTypes.checkTypeEC A; A))
			val () = ExactTypes.checkTypeEC ty
			val () = ExactTypes.noConstrs ()
			val () = ImplicitVars.logicVarsToUCVarsType ty
			val () = ImplicitVars.noUCVars ()
			val ty = Whnf.normalizeType ty
			val ty = PrettyPrint.remDepType ty
			val () = print (id^": Type = "^(PrettyPrint.printType ty)^".\n")
		in TypeAbbrev (id, ty) end
  | reconstructDecl (ObjAbbrev (id, ty, ob)) =
		let val () = ImplicitVars.resetUCTable ()
			val (ob, ty) = ApproxTypes.apxCheckObjEC (ob, ty)
			val ty = Eta.etaExpandType ty
			val ob = Eta.etaExpandObj (ob, asyncTypeToApx ty)
			val () = ImplicitVars.mapUCTable Eta.etaExpandType
			val () = ExactTypes.resetConstrs ()
			val () = ImplicitVars.mapUCTable (fn A => (ExactTypes.checkTypeEC A; A))
			val () = ExactTypes.checkObjEC (ob, ty)
			val () = ExactTypes.noConstrs ()
			val () = ImplicitVars.logicVarsToUCVarsObj (Constraint' (ob, ty))
			val () = ImplicitVars.noUCVars ()
			val ty = Whnf.normalizeType ty
			val ob = Whnf.normalizeObj ob
			val ty = PrettyPrint.remDepType ty
			val ob = PrettyPrint.remDepObj ob
			val () = print (id^": "^(PrettyPrint.printType ty)
							^" = "^(PrettyPrint.printObj ob)^".\n")
		in ObjAbbrev (id, ty, ob) end

(*
fun reconstructDecl (TypeDecl (id, _, ki0)) =
		let val () = ImplicitVars.resetUCTable ()
			val ki1 = ApproxTypes.apxCheckKind (ApproxTypes.emptyCtx, ki0)
			val ki2 = Eta.etaExpandKind ki1
			val () = ExactTypes.resetConstrs ()
			val () = ExactTypes.checkKind (ExactTypes.emptyCtx, ki2)
			val () = ExactTypes.noConstrs ()
			val () = ImplicitVars.logicVarsToUCVarsKind ki2
			val imps1 = ImplicitVars.convertUCVarsImps (ImplicitVars.sort ())
			val imps2 = map (Util.map2 PrettyPrint.remDepType) imps1
			val ki3 = ImplicitVars.convertUCVarsKind imps2 ki2
			val ki4 = PrettyPrint.remDepKind ki3
			val pki = foldr (fn ((x, A), im) => KPi' (x, A, im)) ki4 imps2
			val () = print (id^": "^(PrettyPrint.printKind pki)^".\n")
		in TypeDecl (id, imps2, ki4) end
  | reconstructDecl (ObjDecl (id, _, ty0)) =
		let val () = ImplicitVars.resetUCTable ()
			val ty1 = ApproxTypes.apxCheckType (ApproxTypes.emptyCtx, ty0)
			val ty2 = Eta.etaExpandType ty1
			val () = ExactTypes.resetConstrs ()
			val () = ExactTypes.checkType (ExactTypes.emptyCtx, ty2)
			val () = ExactTypes.noConstrs ()
			val () = ImplicitVars.logicVarsToUCVarsType ty2
			val imps1 = ImplicitVars.convertUCVarsImps (ImplicitVars.sort ())
			val imps2 = map (Util.map2 PrettyPrint.remDepType) imps1
			val ty3 = ImplicitVars.convertUCVarsType imps2 ty2
			val ty4 = PrettyPrint.remDepType ty3
			val pty = foldr (fn ((x, A), im) => TPi' (x, A, im)) ty4 imps2
			val () = print (id^": "^(PrettyPrint.printType pty)^".\n")
		in ObjDecl (id, imps2, ty4) end
*)


(* reconstructSignature : decl list -> unit *)
fun reconstructSignature prog = app (Signatur.sigAddDecl o reconstructDecl) prog


end
