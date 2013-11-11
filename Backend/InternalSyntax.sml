signature TLU_InternalSyntax = TOP_LEVEL_UTIL

structure InternalSyntax =
struct

open VRef

datatype modeModifier = Normal | Destination
datatype mode = Plus | Minus of modeModifier | Star
type modeDecl = mode list

datatype subModality = ID | INT4LIN | INT4AFF | AFF4LIN
datatype modality = INT | AFF | LIN
type cmodality = modality option

datatype lr = L | R
datatype headType = HdMonad | HdAtom of string

datatype ('x, 'ix) pattern = PDepTensor of ('x, 'ix) pattern * ('x, 'ix) pattern
                           | POne
                           | PDown of 'x
                           | PAffi of 'x
                           | PBang of 'ix

type objPattern = (string, string) pattern
type typePattern = (unit, string option) pattern

datatype kind = Type
              | KPi of string option * asyncType * kind

and asyncType = TLPi of typePattern * syncType * asyncType
              | AddProd of asyncType * asyncType
              | TMonad of syncType
              | TAtomic of string * typeSpine
              (* | TAbbrev of string * asyncType *)

and typeSpine = TNil
              | TApp of object * typeSpine

and syncType = LExists of typePattern * syncType * syncType
             | TOne
             | TDown of asyncType
             | TAffi of asyncType
             | TBang of asyncType

and object = LLam of objPattern * object
           | AddPair of object * object
           | Monad of expObj
           | Atomic of head * spine
           | Clo of object * subst

and spine = Nil
          | LApp of monadObj * spine
          | ProjLeft of spine
          | ProjRight of spine
          | SClo of spine * subst

and expObj = Let of (objPattern * (head * spine)) list * monadObj

and monadObj = DepPair of monadObj * monadObj
             | One
             | Down of object
             | Affi of object
             | Bang of object
             | MonUndef

and head = Const of string
         | Var of modality * int
         | UCVar of string
         | LogicVar of {
           X     : object option vref,
           ty    : asyncType,
           s     : subst,
           (* ctx   : asyncType Context.context option ref, *)
           (* cnstr : constr vref list vref, *)
           tag   : int
         }

and subst = Dot of subObj * subst
          | Shift of int

and subObj = Ob of modality * object
           | Idx of subModality * int
           | Undef

type epsilon = (objPattern * (head * spine)) list


datatype typeOrKind = Ty of asyncType | Ki of kind

datatype opSemType = OpSemUnif | OpSemMatch

datatype decl = ConstDecl of string * int * typeOrKind
	| TypeAbbrev of string * asyncType
	| ObjAbbrev of string * asyncType * object
	| Query of opSemType * int option * int option * int option * int * asyncType
	| Trace of int option * syncType
	| Exec of int option * syncType
	| Mode of string * modeDecl option * modeDecl
	| Empty of string


(* heads : asyncType -> (lr list * headType) list *)
fun heads ty =
    case ty of
	TLPi (_, _, A) => heads A
      | AddProd (A, B) => map (map1 (fn lrs => L::lrs)) (heads A)
			  @ map (map1 (fn lrs => R::lrs)) (heads B)
      | TMonad _ => [([], HdMonad)]
      | TAtomic (a, _) => [([], HdAtom a)]


val lVarCnt = ref 0 (* 0w0 *)
val idSubst = Shift 0

fun nextLVarCnt () = (lVarCnt := (!lVarCnt) + 1 (* 0w1 *) ; !lVarCnt)

fun newLVar ty = Atomic (LogicVar {X=vref NONE, ty=ty, s=idSubst, tag=nextLVarCnt ()}, Nil)

fun getDeclId (ConstDecl (s,_,_)) = SOME s
  | getDeclId (TypeAbbrev (s,_)) = SOME s
  | getDeclId (ObjAbbrev (s,_,_)) = SOME s
  | getDeclId (Mode (s,_,_)) = SOME s
  | getDeclId (Empty s) = SOME s
  | getDeclId _ = NONE


(* foldSubst : (substObj * 'a -> 'a) -> (int -> 'a) -> subst -> 'a *)
fun foldSubst f e (Dot (ob, s)) = f (ob, foldSubst f e s)
  | foldSubst f e (Shift n) = e n

(* map : (nfObj -> nfObj) -> subst -> subst *)
fun mapSubst f (Dot (Ob (M, ob), s)) = Dot (Ob (M, f ob) handle ExnUndef => Undef, mapSubst f s)
  | mapSubst f (Dot (Undef, s)) = Dot (Undef, mapSubst f s)
  | mapSubst f (Dot (Idx n, s)) = Dot (Idx n, mapSubst f s)
  | mapSubst f (Shift n) = Shift n



(* infix with'ty with's *)
(* fun {X, ty=_, s, tag} with'ty ty' = {X=X, ty=ty', s=s, tag=tag} *)
(* fun {X, ty, s=_, tag} with's s' = {X=X, ty=ty, s=s', tag=tag} *)

fun updTy {X, ty=_, s, tag} ty' = {X=X, ty=ty', s=s, tag=tag}
fun updS {X, ty, s=_, tag} s' = {X=X, ty=ty, s=s', tag=tag}


fun numBinds (PDepTensor (p1,p2)) = numBinds p1 + numBinds p2
  | numBinds POne = 0
  | numBinds (PDown _) = 1
  | numBinds (PAffi _) = 1
  | numBinds (PBang _) = 1


fun patternMap f g (PDepTensor (p1, p2)) = PDepTensor (patternMap f g p1, patternMap f g p2)
  | patternMap f g POne = POne
  | patternMap f g (PDown x) = PDown (f x)
  | patternMap f g (PAffi x) = PAffi (f x)
  | patternMap f g (PBang x) = PBang (g x)

val patternTypeToObj = patternMap (fn () => "") (fn x => getOpt (x, ""))


fun patternAddDep (p1, p2) = case (p1, p2) of
	  (PDepTensor (p11, p12), PDepTensor (p21, p22)) =>
		PDepTensor (patternAddDep (p11, p21), patternAddDep (p12, p22))
	| (POne, POne) => POne
	| (PDown (), PDown ()) => PDown ()
	| (PAffi (), PAffi ()) => PAffi ()
	| (PBang NONE, PBang NONE) => PBang NONE
	| (PBang (SOME x), PBang NONE) => PBang (SOME x)
	| (PBang NONE, PBang (SOME x)) => PBang (SOME x)
	| (PBang (SOME x), PBang (SOME _)) => PBang (SOME x)
	| _ => raise Fail "Internal error: patternAddDep pattern mismatch"


end
