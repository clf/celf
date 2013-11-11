signature TLU_PrettyPrinting = TOP_LEVEL_UTIL
structure PrettyPrinting :> PRETTY_PRINTING =
struct

open InternalSyntax

structure RAList = RandomAccessList
structure ST = StringRedBlackTree

val printImpl = ref false

fun printModality INT = "!"
  | printModality AFF = "@"
  | printModality LIN = "L"

fun printSubModality ID = ""
  | printSubModality INT4LIN = "!/L"
  | printSubModality INT4AFF = "!/@"
  | printSubModality AFF4LIN = "@/L"


(* isNat : some type of obj -> int option *)
fun isNat x =
    case x of
      Atomic (Const "s", S) =>
      ( case S of
          LApp (M, S') =>
          ( case (M, S') of
                (Bang N, Nil) => ( case N of
                                       P as Atomic _ =>
                                       ( case isNat P of
                                             SOME n => SOME (n+1)
                                           | NONE => NONE )
                                     | _ => NONE )
              | _ => NONE )
         | _ => NONE )
     | Atomic (Const "z", S) =>
       ( case S of
             Nil => SOME 0
           | _ => NONE )
     | _ => NONE

fun join' [] = []
  | join' [x] = x
  | join' (x::xs) = x @ ["] ["] @ join' xs
val join = (fn [] => [] | xs => ["[["] @ xs @ ["]]"]) o join'

fun paren false x = x
  | paren true x = ["("] @ x @ [")"]

fun lookup ctx n = RAList.lookup ctx (n-1)
    handle RAList.Subscript => Int.toString (n - RAList.length ctx)

(* indexTable keeps track of the largest index used to build a variable name *)
(* indexTable(X) = k means that "X{k+1}" should be a fresh name *)
val indexTable : int ST.Table = ST.new 0

(* add : string -> string RAList.ralist -> (string, string RAList.ralist *)
(* add x ctx = (x', ctx') iff
 * - x' = x ^ <number> or x' = X ^ <number>  when x = ""
 * - x' is fresh in ctx
 * - ctx' is obtained by adding x to ctx
 *)
fun add x ctx =
    let
      fun fresh x = x ^ Int.toString (case ST.lookup indexTable x of
                                        NONE => (ST.insert indexTable (x, 1); 1)
                                      | SOME n => (ST.insert indexTable (x, n+1); n+1))
      fun tryAdd x = if RAList.exists (fn y => x=y) ctx then fresh (x^"_") else x
      val varName = if x="" then fresh "X" else tryAdd x
    in
      (varName, RAList.cons varName ctx)
    end

fun addNoOccur ctx = RAList.cons "? Error ?" ctx

val noSkip = ref false
fun getImplLength c = if !noSkip then 0 else Signature.getImplicitNum c

fun pKind ctx ki =
    case ki of
        Type => ["type"]
      | KPi (NONE, A, K) => pType ctx true A @ [" -> "] @ pKind ctx K
      | KPi (SOME x, A, K) =>
        let val (x', ctx') = add x ctx
        in ["Pi "^x'^": "] @ pType ctx false A @ [". "] @ pKind ctx' K end
and pType ctx pa ty =
    case ty of
        TLPi (p, S, B) =>
        paren pa (case (p, S) of
                      (PBang NONE, TBang A) =>
                      pType ctx true A @ [" -> "] @ pType (addNoOccur ctx) false B
                    | (PBang (SOME x), TBang A) =>
                      let
                        val (x', ctx') = add x ctx
                      in
                        ["Pi "^x'^": "] @ pType ctx false A @ [". "] @ pType ctx' false B
                      end
                    | (PAffi (), TAffi A) =>
                      pType ctx true A @ [" -@ "] @ pType (addNoOccur ctx) false B
                    | _ =>
                      let
                        val (pP, ctx', d) = pTPattern ctx p
                      in
                        if d
                        then ["PI "] @ pP @ [": "] @ pSyncType ctx false S @ [". "] @ pType ctx' false B
                        else pSyncType ctx true S @ [" -o "] @ pType ctx' false B
                      end)
      | AddProd (A, B) => paren pa (pType ctx true A @ [" & "] @ pType ctx true B)
      | TMonad S => ["{"] @ pSyncType ctx false S @ ["}"]
      | TAtomic (a, S) => [a] @  pTypeSpineSkip ctx S (getImplLength a)
and pTypeSpineSkip ctx sp n =
    if n=0
    then pTypeSpine ctx sp
    else case sp of
             TNil => raise Fail "Internal error: pTypeSpineSkip"
           | TApp (N, S) =>
             (if !printImpl then [" <"] @ pObj ctx false N @ [">"] else [])
             @ pTypeSpineSkip ctx S (n-1)
and pTypeSpine ctx sp =
    case sp of
      TNil => []
    | TApp (N, S) => [" "] @ pObj ctx true N @ pTypeSpine ctx S
and pSyncType ctx pa sty =
    case sty of
      LExists (p, S1, S2) =>
      paren pa (case (p, S1) of
                  (PBang (SOME x), TBang A) =>
                  let
                    val (x', ctx') = add x ctx
                  in
                    ["Exists "^x'^": "] @ pType ctx false A @ [". "] @ pSyncType ctx' false S2
                  end
                | _ =>
                  let
                    val (pP, ctx', d) = pTPattern ctx p
                  in
                    if d
                    then ["EXISTS "] @ pP @ [": "] @ pSyncType ctx false S1 @ [". "]
                         @ pSyncType ctx' false S2
                    else pSyncType ctx true S1 @ [" * "] @ pSyncType ctx' true S2
                  end)
    | TOne => ["1"]
    | TDown A => pType ctx pa A
    | TAffi A => ["@"] @ pType ctx true A
    | TBang A => ["!"] @ pType ctx true A
and pObj ctx pa ob =
    case ob of
        LLam (p, N) =>
        let val (pP, ctx') = pOPattern ctx p
        in paren pa (["\\"] @ pP @ [". "] @ pObj ctx' false N) end
      | AddPair (N1, N2) => ["<"] @ pObj ctx false N1 @ [", "] @ pObj ctx false N2 @ [">"]
      | Monad E => ["{"] @ pExp ctx E @ ["}"]
      | Atomic (H, S) =>
        let
          val skip = case H of Const c => getImplLength c | _ => 0
          val c = case H of Const c => c | _ => "none"
        in
          case isNat ob of
              SOME n => ["N"^Int.toString n]
            | NONE =>
              ( case (pHead ctx H, pSpineSkip c ctx S skip) of
                    (h, []) => h
                  | (h, s) => paren pa (h @ s)
              )
        end
      | Clo (ob, sp) => raise Fail "Internal error: pObj Clo"
and pHead ctx h =
    case h of
        Const c => [c]
      | Var (M, n) => [lookup ctx n, case M of INT => "!" | AFF => "@" | LIN => "L", "[", Int.toString n, "]"]
      | UCVar v => ["#"^v]
      | LogicVar {ty, s, tag, ...} =>
        ["$", Int.toString tag]
        @ [printSubst s]
(* and pContextOpt NONE = ["--"] *)
(*   | pContextOpt (SOME G) = ["["] @ (#2 $ pContext $ Context.ctx2list G) @ ["]"] *)
(* and pContext [] = ([], []) *)
(*   | pContext ((x, A, m)::G) = *)
(*     let val (ctx, pG) = pContext G *)
(*         val (x', ctx') = add x ctx *)
(*         (* FIXME: Reverse order for better ctx printing, make ctx an argument *) *)
(*         fun pM NONE = " NO" *)
(*           | pM (SOME Context.INT) = " !" *)
(*           | pM (SOME Context.AFF) = " @" *)
(*           | pM (SOME Context.LIN) = " L" *)
(*         val pTy = if !printLVarCtx > 1 then [" : "] @ pType ctx false A else [] *)
(*     in (ctx', ["["] @ [x'] @ [pM m] @ pTy @ ["]"] @ pG) end *)
and pSpineSkip c ctx sp n =
    if n=0
    then pSpine ctx sp
    else case sp of
           LApp (M, S) =>
           (if !printImpl then [" <"] @ pMonadObj ctx false M @ [">"] else [])
           @ pSpineSkip c ctx S (n-1)
         | _ => raise Fail ("Internal error: pSpineSkip " ^ c ^ "(" ^ String.concat (pSpine ctx sp) ^ ") [" ^ Int.toString n ^ "]")
and pSpine ctx sp =
    case sp of
      Nil => []
    | LApp (M, S) => [" "] @ pMonadObj ctx true M @ pSpine ctx S
    | ProjLeft S => [" #1"] @ pSpine ctx S
    | ProjRight S => [" #2"] @ pSpine ctx S
    | SClo (S, s) => raise Fail "Internal error: pSpine SClo"

and pExp ctx (Let (eps, m)) =
    let
      fun pStep ((p, (h, sp)), (r, ctx)) =
          let
            val (pP, ctx') = pOPattern ctx p
          in
            (r @ ["{" ^ String.concat pP ^ "} = " ^ String.concat (pObj ctx false (Atomic (h,sp)))], ctx')
          end
      val (ps, ctx1) = List.foldl pStep ([], ctx) eps
      val ps1 =
          case ps of
              [] => ["\n    let {}"]
            | x::xs => ("\n    let " ^ x) :: map (fn y => "\n      ; "^y) xs
      val pm = pMonadObj ctx1 false m
    in
      ps1 @ [" in "] @ pm
    end
and pMonadObj ctx pa m =
    case m of
      DepPair (M1, M2) => ["["] @ pMonadObj ctx false M1 @ [", "] @ pMonadObj ctx false M2 @ ["]"]
    | One => ["1"]
    | Down N => pObj ctx pa N
    | Affi N => ["@"] @ pObj ctx true N
    | Bang N => ["!"] @ pObj ctx true N
    | MonUndef => ["????"]

and pOPattern bctx p =
    case p of
      PDepTensor (p1, p2) =>
      let
        val (pP1, bctx') = pOPattern bctx p1
        val (pP2, bctx'') = pOPattern bctx' p2
      in
        (["["] @ pP1 @ [", "] @ pP2 @ ["]"], bctx'')
      end
    | POne => (["1"], bctx)
    | PDown x => map1 (fn x => [x]) (add x bctx)
    | PAffi x => map1 (fn x => ["@"^x]) (add x bctx)
    | PBang x => map1 (fn x => ["!"^x]) (add x bctx)
and pTPattern bctx p =
    case p of
      PDepTensor (p1, p2) =>
      let val (pP1, bctx', d1) = pTPattern bctx p1
          val (pP2, bctx'', d2) = pTPattern bctx' p2
      in (["["] @ pP1 @ [", "] @ pP2 @ ["]"], bctx'', d1 orelse d2) end
    | POne => (["1"], bctx, false)
    | PDown () => (["_"], addNoOccur bctx, false)
    | PAffi () => (["@_"], addNoOccur bctx, false)
    | PBang NONE => (["!_"], addNoOccur bctx, false)
    | PBang (SOME x) => let val (x', bctx') = add x bctx in (["!"^x'], bctx', true) end

and printSubObj (Ob (m, ob)) = (String.concat (pObj [] true ob) handle ExnUndef => "_") ^"/"^ printModality m
  | printSubObj (Idx (m, k)) = Int.toString k ^ printSubModality m
  | printSubObj Undef = "_"

and printSubst s =
    let
      fun pSubst (Dot (m, s)) = printSubObj m ^ "." ^ pSubst s
        | pSubst (Shift k) = "^" ^ Int.toString k
    in
      "["^ pSubst s ^"]"
    end

fun printMode Plus = "+"
  | printMode (Minus Normal) = "-"
  | printMode (Minus Destination) = "-D"
  | printMode Star = "*"

val printKind = String.concat o (pKind [])
val printType = String.concat o (pType [] false) o InternalSubst.normalizeType
val printTypeInCtx = fn ctx => String.concat o (pType (RandomAccessList.fromList ctx) false)
val printSyncType = String.concat o (pSyncType [] false) o InternalSubst.normalizeSyncType
val printObj = String.concat o (pObj [] false) o InternalSubst.normalizeObj
val printObjInCtx = fn ctx => String.concat o (pObj (RandomAccessList.fromList ctx) false)
val printMonadObj = String.concat o (pMonadObj [] false)


fun printOptInt NONE = "*"
  | printOptInt (SOME n) = Int.toString n

fun intercalate [] = ""
  | intercalate [x] = x
  | intercalate (x::y::ys) = x ^ " " ^ intercalate (y::ys)

fun printDecl (ConstDecl (id,_,Ki ki)) =
    id ^ ": " ^ printKind ki ^ "."
  | printDecl (ConstDecl (id,_,Ty ty)) =
    id ^ ": " ^ printType ty ^ "."
  | printDecl (TypeAbbrev (id, ty)) =
    "type " ^ id ^ " = " ^ printType ty
  | printDecl (ObjAbbrev (id, ty, obj)) =
    "obj " ^ id ^ " : " ^ printType ty ^ " = " ^ printObj obj
  | printDecl (Query (t,n1,n2,n3,n4,ty)) =
    let
      val pt = case t of
                   OpSemUnif => "#query"
                 | OpSemMatch => "#mquery"
    in
      intercalate [ pt
                  , printOptInt n1
                  , printOptInt n2
                  , printOptInt n3
                  , Int.toString n4
                  , printType ty ^ "." ]
    end
  | printDecl (Trace (n, ty)) =
    intercalate ["#trace", printOptInt n, printSyncType ty ^ "."]
  | printDecl (Exec (n, ty)) =
    intercalate ["#exec", printOptInt n, printSyncType ty ^ "."]
  | printDecl (Mode (id, implmd, md)) =
    intercalate [ "#mode"
                , id
                , "{"
                , Option.getOpt (Option.map (intercalate o map printMode) implmd, "")
                , "}"
                , intercalate (map printMode md) ]
  | printDecl (Empty s) = "#empty " ^ s ^ "."

fun printPreObj ob = ( noSkip := true; (String.concat o (pObj [] false)) ob before noSkip := false )

end
