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

signature TLU_OpSemModed = TOP_LEVEL_UTIL
structure OpSemModed :> OPSEM =
struct

open Syntax
(* open PatternBind *)
open SignaturTable

val traceSolve = ref 0
val allowConstr = ref false
val debugForwardChaining = ref false

val fcLimit = ref NONE : int option ref

val dummyObj : obj = LLam' (POne', Monad' (Mon' One'))
val dummyMonadObj : monadObj = One'
val dummyExpObj : expObj = Mon' One'
val dummySpine : spine = LApp' (One', Nil')

(* The type 'context' represents input and output contexts and the type
 * 'lcontext' represents the part of the input context that has to occur
 * at that specific point, i.e. it is not allowed to be passed to the
 * output context. *)
type headedType = asyncType * (lr list * headType) list
type context = headedType OpSemCtx.context
type lcontext = int list (* must-occur context: list of indices *)


(* Printing out contexts that arise during forward chaining *)

(* Prepare the context for printing in a very loose sense. *)
(* Invariant: The head of "context" is always the i+1th element of the
 * original context. We're walking through both lists in tandem, noticing
 * when lcontext is telling us that we're at a mandatory item.
 *
 * It may not actually be the case that we need the lcontext at all - if
 * we look at the overlap, it appears that all the information we need
 * comes from whether the context-thing is persistent, affine, linear, or
 * gone. -rjs 2012-03-29 *)
fun prepCtx (lcontext, i, context) =
    let
      fun modalityStr Context.INT = "pers"
        | modalityStr Context.AFF = "aff"
        | modalityStr Context.LIN = "lin"

      (* What is this "stuff"? The rest of the file indicates they're
       * some sort of oracle-y thing? -rjs 2012-03-29 *)
      fun dataStr (asyncType: Syntax.asyncType,
                   stuff: (SignaturTable.lr list * SignaturTable.headType) list) =
          let
            (* XXX PERF we do this over and over, quadratic *)
            val context' = map #1 (tl context)
          in
            PrettyPrint.printTypeInCtx context' asyncType
          end

      fun optionalItem (varname, data, NONE) =
          [] (* Item removed from ctx *)
        | optionalItem (varname, data, SOME Context.LIN) =
          (* If we are just reporting the intermediate contexts from
           * forward chaining, it should be the case that everything in
           * the context is required to be in the output context: the
           * more interesting case for "maybe used" contexts should only
           * arise during backward chaining proof search, I think. -rjs 2012-03-29 *)
          [ "surprised that this happened!!!" ]
        | optionalItem (varname, data, SOME Context.AFF) =
          [ dataStr data^" aff" ]
        | optionalItem (varname, data, SOME Context.INT) =
          (* This seemed to work on the simple examples - is it really
           * as simple as saying that the variable-stuff has names and
           * the resource-stuff has a varname of emptystring? It's
           * certainly a reasonable approximation - rjs 2012-03-29 *)
          if varname = "" then [ dataStr data ^ " pers" ]
          else [ varname^":"^dataStr data ]

      fun mandatoryItem (varname, data, NONE) =
          raise Fail "Invariant: mandatory item cannot also be removed from context!"
        | mandatoryItem (varname, data, SOME Context.LIN) =
          [ dataStr data^" lin" ]
        | mandatoryItem (varname, data, SOME modality) =
          (* Linear things are the only ones required to be in the context *)
          raise Fail "Invariant: Only linear things should be required!"
    in
      case (lcontext, context) of
        ([], []) => []
      | ([], x :: xs) => optionalItem x @ prepCtx (lcontext, i+1, xs)
      | (j :: js, []) => [] (* raise Fail "Invariant: lcontext doesn't match context" *)
      | (j :: js, x :: xs) =>
        if j < i then raise Fail "Invariant: j < i should be impossible"
        else if j = i then mandatoryItem x @ prepCtx (js, i+1, xs)
        else optionalItem x @ prepCtx (lcontext, i+1, xs)
    end

and printCtx (_, context) =
    let
      (* XXX PERF - Pretty terrible (quadratic at least) -rjs 2012-03-29 *)
      fun rename [] = []
        | rename ((item as (x, _, _)) :: context) =
          let
            val context' = rename context
            fun inlist z = List.exists (fn (y,_,_) => z = y) context'
            fun loop x i =
                if inlist (x^"_"^Int.toString i)
                then loop x (i+1) else (x^"_"^Int.toString i)
          in
            if x = "" then item :: context'
            else if inlist x then (loop x 1, #2 item, #3 item) :: context'
            else item :: context'
          end

      fun layout n [] = print "(nothing)\n"
        | layout n [ x ] =
          if n + size x > 80 then print ("\n   "^x^"\n") else print (x^"\n")
        | layout n (x :: xs) =
          if n + size x + 2 > 80
          then (print ("\n   "^x^", "); layout (size x + 5) xs)
          else (print (x^", "); layout (n + size x + 2) xs)

      val printableCtx = prepCtx (OpSemCtx.linearIndices context, 1, rename (OpSemCtx.ctx2list context))
    in
      print "-- "; layout 3 (rev printableCtx)
    end

(* matchCtxGoalPattern : context * goalPattern -> bool *)
fun matchCtxGoalPattern (_, NONE) = true
  | matchCtxGoalPattern (ctx : context, SOME (c, arg)) =
    let
      fun matchType ty =
          case AsyncType.prj ty of
            TAtomic (c', S) =>
            if c = c'
            then
              ( case (arg, TypeSpine.prj S) of
                  (SOME constr, TApp (N, _)) =>
                  ( case Obj.prj N of
                      Atomic (Const constr', _) => constr = constr'
                    | _ => false )
                | (NONE, _) => true
                | _ => false )
            else false
          | _ => false
    in
      case OpSemCtx.findNonDep (fn (_, _, (ty, _), _) => matchType ty) ctx of
        SOME (_, id, (ty, _), _) =>
        ( if !traceSolve >= 2
          then print ("found "^id^": "^PrettyPrint.printType ty^"\n")
          else ()
        ; true )
      | NONE =>
        ( if !traceSolve >= 2
          then print "not found\n"
          else ()
        ; false )
    end


(* bind2list : pattern * syncType -> (string * modality * headedType) list *)
fun bind2list (p, sty) : (string * Context.modality * headedType) list =
    case (Pattern.prj p, SyncType.prj sty) of
      (PDepTensor (p1, p2), LExists (p1', S1, S2)) =>
      bind2list (Util.patternAddDep (p1, p1'), S1) @ bind2list (p2, S2)
    | (POne, TOne) => []
    | (PDown x, TDown A) => [("", Context.LIN, (A, heads A))]
    | (PAffi x, TAffi A) => [("", Context.AFF, (A, heads A))]
    | (PBang NONE, TBang A) => [("", Context.INT, (A, heads A))]
    | (PBang (SOME x), TBang A) => [(x, Context.INT, (A, []))]
    | _ => raise Fail "Internal error: bind2list"

fun pBindLCtx p l =
    let
      fun bind (n, p, l) =
          case Pattern.prj p of
            PDepTensor (p1, p2) => bind (n, p2, bind (n + nbinds p2, p1, l))
          | PDown _ => n::l
          | _ => l (* POne, PAffi, PBang *)
    in
      bind (1, p, map (fn k => k + nbinds p) l)
    end

fun pushBind (p, sty) ctx : context = OpSemCtx.ctxPushList (bind2list (p, sty)) ctx


(* partitionArgs : string * typeSpine -> obj list * obj list *)
fun partitionArgs (a, S) =
    let
      fun partArgs (S, md) = case (TypeSpine.prj S, md) of
                               (TNil, []) => ([], [])
                             | (TApp (N, S'), m :: md') =>
                               let
                                 val (inp, outp) = partArgs (S', md')
                               in
                                 case m of
                                   Plus => (N :: inp, outp)
                                 | Minus _ => (inp, N :: outp)
                                 | Star => raise Fail "Star should not happen?"
                               end
                             | _ => raise Fail "Internal error: partArgs"
      val md = case Signatur.getModeDecl a of
                 SOME x => x
               | NONE => raise Fail (a ^ " should be moded.")
    in
      partArgs (S, md)
    end

(* decomposeAtomic : lr list * context * asyncType
                     -> (obj list * (modality * asyncType) list * obj list * (monadObj list -> spine) *)
fun decomposeAtomic (lr, ctx : context, ty) =
    let
      val intCtx = ref (SOME Context.emptyCtx) (* NONE *)
      fun getIntCtx () = case !intCtx of
                           SOME G => SOME G
                         | NONE => ( intCtx := (SOME $ Context.sparseList2ctx $ List.map (fn (k,x,(ty,_),m)=>(k,x,ty,m)) (OpSemCtx.depPart ctx)) ; getIntCtx () )

      (* decompAtomic : lr list * asyncType
                        -> (obj list * (modality * asyncType) list * obj list * (monadObj list -> spine) *)
      fun decompAtomic (lr, ty) =
          case Util.typePrjAbbrev ty of
            TLPi (p, A, B) =>
            let
              val (subgoalsA, mkMonadObj, m) = decompAtomicSync (p, A)
              val B' = TClos (B, Subst.subM $ normalizeMonadObj m)
              val (Sin, subgoalsB, Sout, mkSpine) = decompAtomic (lr, B')
              val numgoalsB = List.length subgoalsB
            in
              (Sin, subgoalsB @ subgoalsA, Sout,
               (fn objs =>
                   let
                     val (objsB, objsA) = partitionAt numgoalsB objs
                   in
                     LApp' (mkMonadObj objsA, mkSpine objsB)
                   end))
            end
          | AddProd (A, B) =>
            let
              val (ty', proj) = case List.hd lr of (* Invariant: lr <> [] *)
                                  L => (A, ProjLeft')
                                | R => (B, ProjRight')
              val (Sin, subgoals, Sout, mkSpine) = decompAtomic (List.tl lr, ty')
            in
              (Sin, subgoals, Sout, proj o mkSpine)
            end
          | TMonad S => raise Fail "Internal error: decompAtomic applied to monadic hypothesis!"
          | TAbbrev _ => raise Fail "Internal error: decompAtomic: TAbbrev"
          | P' as TAtomic (a, S) =>
            let
              val (Sin, Sout) = partitionArgs (a, S)
            in
              (Sin, [], Sout, fn _ (* = [] *) => Nil')
            end

      (* decompAtomicSync : pattern * syncType
                            -> ((modality * asyncType) list * (monadObj list -> monadObj) * monadObj *)
      and decompAtomicSync (p, sty) =
          case (Pattern.prj p, SyncType.prj sty) of
            (PDepTensor (p1, p2), LExists (p1', S1, S2)) =>
            let
              val (subgoals1, mkMonadObj1, m1) = decompAtomicSync (Util.patternAddDep (p1, p1'), S1)
              val S2' = STClos (S2, Subst.subM $ normalizeMonadObj m1)
              val (subgoals2, mkMonadObj2, m2) = decompAtomicSync (p2, S2')
              val numgoals1 = List.length subgoals1
              fun mkMonadObj xs =
                  let
                      val (goals1, goals2) = partitionAt numgoals1 xs
                  in
                    DepPair' (mkMonadObj1 goals1, mkMonadObj2 goals2)
                  end
              in
              (subgoals1 @ subgoals2, mkMonadObj, DepPair' (m1, m2))
            end
          | (POne, TOne) => ([], fn _ (* = [] *) => One', One')
          | (PDown (), TDown A) => ([(Context.LIN, A)], fn Ns (* = [_] *) => Down' (List.hd Ns), MonUndef')
          | (PAffi (), TAffi A) => ([(Context.AFF, A)], fn Ns (* = [_] *) => Affi' (List.hd Ns), MonUndef')
          | (PBang NONE, TBang A) => ([(Context.INT, A)], fn Ns (* = [_] *) => Bang' (List.hd Ns), MonUndef')
          | (PBang (SOME x), TBang A) =>
              let
                val X = newLVarCtx (getIntCtx ()) A
              in
                ([], fn _ (* = [] *) => Bang' X, Bang' X)
              end
          | _ => raise Fail "Internal error: decompAtomicSync"
    in
      decompAtomic (lr, ty)
    end


(* decomposeMonadic : lr list * context * asyncType
                      -> ((modality * asyncType) list * (monadObj list -> spine) * syncType *)
fun decomposeMonadic (lr, ctx : context, ty) =
    let
      val intCtx = ref (SOME Context.emptyCtx) (* NONE *)
      fun getIntCtx () = case !intCtx of
                           SOME G => SOME G
                         | NONE => ( intCtx := (SOME $ Context.sparseList2ctx $ List.map (fn (k,x,(ty,_),m)=>(k,x,ty,m)) (OpSemCtx.depPart ctx)) ; getIntCtx () )

      (* decompMonadic : lr list * asyncType
                         -> ((modality * asyncType) list * (monadObj list -> spine) * syncType *)
      fun decompMonadic (lr, ty) =
          case Util.typePrjAbbrev ty of
            TLPi (p, A, B) =>
            let
              val (subgoalsA, mkMonadObj, m) = decompMonadicSync (p, A)
              val B' = TClos (B, Subst.subM $ normalizeMonadObj m)
              val (subgoalsB, mkSpine, sty) = decompMonadic (lr, B')
              val numgoalsB = List.length subgoalsB
            in
              (subgoalsB @ subgoalsA
             , fn objs =>
                  let
                    val (objsB, objsA) = partitionAt numgoalsB objs
                  in
                    LApp' (mkMonadObj objsA, mkSpine objsB)
                  end
             , sty)
            end
          | AddProd (A, B) =>
            let
              val (ty', proj) = case List.hd lr of (* Invariant: lr <> [] *)
                                  L => (A, ProjLeft')
                                | R => (B, ProjRight')
              val (subgoals, mkSpine, sty) = decompMonadic (List.tl lr, ty')
            in
              (subgoals, proj o mkSpine, sty)
            end
          | TMonad S => ([], fn _ (* [] *) => Nil', S)
          | TAbbrev _ => raise Fail "Internal error: decompMonadic: TAbbrev"
          | P' as TAtomic _ => raise Fail "Internal error: decompMonadic applied to atomic hypothesis!"

      (* decompMonadicSync : pattern * syncType
                             -> ((modality * asyncType) list * (monadObj list -> monadObj) * monadObj *)
      and decompMonadicSync (p, sty) =
          case (Pattern.prj p, SyncType.prj sty) of
            (PDepTensor (p1, p2), LExists (p1', S1, S2)) =>
            let
              val (subgoals1, mkMonadObj1, m1) = decompMonadicSync (Util.patternAddDep (p1, p1'), S1)
              val S2' = STClos (S2, Subst.subM $ normalizeMonadObj m1)
              val (subgoals2, mkMonadObj2, m2) = decompMonadicSync (p2, S2')
              val numgoals1 = List.length subgoals1
              fun mkMonadObj xs =
                  let
                      val (goals1, goals2) = partitionAt numgoals1 xs
                  in
                    DepPair' (mkMonadObj1 goals1, mkMonadObj2 goals2)
                  end
              in
              (subgoals1 @ subgoals2, mkMonadObj, DepPair' (m1, m2))
            end
          | (POne, TOne) => ([], fn _ (* = [] *) => One', One')
          | (PDown (), TDown A) => ([(Context.LIN, A)], fn Ns (* = [_] *) => Down' (List.hd Ns), MonUndef')
          | (PAffi (), TAffi A) => ([(Context.AFF, A)], fn Ns (* = [_] *) => Affi' (List.hd Ns), MonUndef')
          | (PBang NONE, TBang A) => ([(Context.INT, A)], fn Ns (* = [_] *) => Bang' (List.hd Ns), MonUndef')
          | (PBang (SOME x), TBang A) =>
              let
                val X = newLVarCtx (getIntCtx ()) A
              in
                ([], fn _ (* = [] *) => Bang' X, Bang' X)
              end
          | _ => raise Fail "Internal error: decompMonadicSync"
    in
      decompMonadic (lr, ty)
    end


(* decomposeSync : context  * syncType
                   -> ((modality * asyncType) list * (monadObj list -> monadObj) *)
fun decomposeSync (ctx : context, sty) =
    let
      val intCtx = ref (SOME Context.emptyCtx) (* NONE *)
      fun getIntCtx () = case !intCtx of
                           SOME G => SOME G
                         | NONE => ( intCtx := (SOME $ Context.sparseList2ctx $ List.map (fn (k,x,(ty,_),m)=>(k,x,ty,m)) (OpSemCtx.depPart ctx)) ; getIntCtx () )

      (* decompSync : pattern * syncType
                      -> ((modality * asyncType) list * (monadObj list -> monadObj) * monadObj *)
      fun decompSync (p, sty) =
          case (Pattern.prj p, SyncType.prj sty) of
            (PDepTensor (p1, p2), LExists (p1', S1, S2)) =>
            let
              val (subgoals1, mkMonadObj1, m1) = decompSync (Util.patternAddDep (p1, p1'), S1)
              val S2' = STClos (S2, Subst.subM $ normalizeMonadObj m1)
              val (subgoals2, mkMonadObj2, m2) = decompSync (p2, S2')
              val numgoals1 = List.length subgoals1
              fun mkMonadObj xs =
                  let
                      val (goals1, goals2) = partitionAt numgoals1 xs
                  in
                    DepPair' (mkMonadObj1 goals1, mkMonadObj2 goals2)
                  end
              in
              (subgoals1 @ subgoals2, mkMonadObj, DepPair' (m1, m2))
            end
          | (POne, TOne) => ([], fn _ (* = [] *) => One', One')
          | (PDown (), TDown A) => ([(Context.LIN, A)], fn Ns (* = [_] *) => Down' (List.hd Ns), MonUndef')
          | (PAffi (), TAffi A) => ([(Context.AFF, A)], fn Ns (* = [_] *) => Affi' (List.hd Ns), MonUndef')
          | (PBang NONE, TBang A) => ([(Context.INT, A)], fn Ns (* = [_] *) => Bang' (List.hd Ns), MonUndef')
          | (PBang (SOME x), TBang A) =>
              let
                val X = newLVarCtx (getIntCtx ()) A
              in
                ([], fn _ (* = [] *) => Bang' X, Bang' X)
              end
          | _ => raise Fail "Internal error: decompSync"

      (* decompSync' : syncType
                       -> ((modality * asyncType) list * (monadObj list -> monadObj) * monadObj *)
      fun decompSync' sty =
          case SyncType.prj sty of
            LExists (p1, S1, S2) =>
            let
              val (subgoals1, mkMonadObj1, m1) = decompSync (p1, S1)
              val S2' = STClos (S2, Subst.subM $ normalizeMonadObj m1)
              val (subgoals2, mkMonadObj2, m2) = decompSync' S2'
              val numgoals1 = List.length subgoals1
              fun mkMonadObj xs =
                  let
                      val (goals1, goals2) = partitionAt numgoals1 xs
                  in
                    DepPair' (mkMonadObj1 goals1, mkMonadObj2 goals2)
                  end
              in
              (subgoals1 @ subgoals2, mkMonadObj, DepPair' (m1, m2))
            end
          | TOne => ([], fn _ (* = [] *) => One', One')
          | TDown A => ([(Context.LIN, A)], fn Ns (* = [_] *) => Down' (List.hd Ns), MonUndef')
          | TAffi A => ([(Context.AFF, A)], fn Ns (* = [_] *) => Affi' (List.hd Ns), MonUndef')
          | TBang A => ([(Context.INT, A)], fn Ns (* = [_] *) => Bang' (List.hd Ns), MonUndef')


      val (subgoals, mkMonadObj, _) = decompSync' sty
    in
      (subgoals, mkMonadObj)
    end

fun traceLeftFocus (h, ty) =
    if !traceSolve >= 2 then
      print ("Trying "^PrettyPrint.printPreObj (Atomic' (h, Nil'))^
             " : "^PrettyPrint.printType ty^"\n")
    else ()

val totalCtxLength = ref 0
val totalAvailLength = ref 0

fun syncType2pat sty =
    case SyncType.prj sty of
      LExists (p, _, S2) => PDepTensor' (p, syncType2pat S2)
    | TOne => POne'
    | TDown A => PDown' ()
    | TAffi A => PAffi' ()
    | TBang A => PBang' NONE

(* solve : bool * context * asyncType * (obj * context -> unit) -> unit *)
(* Right Inversion : Gamma;Delta => A *)
fun solve (consumeAll, ctx, ty, sc) =
    ( if !traceSolve >= 3 then
        print ("Right Invert ("^PrettyPrint.printType ty^")\n")
      else ()
    ; solve' (consumeAll, ctx, ty, sc) )
and solve' (consumeAll, ctx, ty, sc) =
    case Util.typePrjAbbrev ty of
      TLPi (p, S, A) => solve (consumeAll, pushBind (p, S) ctx, A,
                            (* The pattern p is a type pattern, which means that
                             * it only names dependent variables. We need to create
                             * p', the term pattern, which binds all the
                             * variables; Util.patternT2O does this. *)
                            fn (N, ctxo) =>
                               let
                                 val p' = Util.patternT2O p
                               in
                                 sc ((* dummyObj *) LLam' (p', N), OpSemCtx.ctxPopNum (nbinds p') ctxo)
                               end)
    | AddProd (A, B) =>
      if consumeAll
      then
        solve (true, ctx, A, fn (N1, ctxo1) =>
        solve (true, ctx, B, fn (N2, ctxo2) =>
        sc ((* dummyObj *) AddPair' (N1, N2), OpSemCtx.affIntersect(ctxo1, ctxo2))))
      else
        solve (false, ctx, A, fn (N1, ctxo1) =>
        solve (true, OpSemCtx.linearDiff (ctx, ctxo1), B, fn (N2, ctxo2) =>
        sc ((* dummyObj *) AddPair' (N1, N2), OpSemCtx.affIntersect(ctxo1, ctxo2))))
    | TMonad S => forwardChain (!fcLimit, consumeAll, ctx, S, fn (E, ctxo) => sc ((* dummyObj *) Monad' E, ctxo))
    | P as TAtomic (a, _) => if Signatur.hasEmptyDecl a
                             then matchAtomEmpty (consumeAll, ctx, P, sc)
                             else matchAtom (consumeAll, ctx, P, sc)
    | TAbbrev _ => raise Fail "Internal error: solve: TAbbrev"


(* solveList : bool * context -> asyncType list -> (obj list * ctx -> unit) *)
and solveList (consumeAll, ctx) [] sc =
    if consumeAll andalso OpSemCtx.nolin ctx orelse not consumeAll
    then sc ([], ctx)
    else ()
  | solveList (consumeAll, ctx) ((md, G)::gs) sc =
    let
      val filterCtx = case md of
                        Context.LIN => (fn x => x)
                      | Context.AFF => OpSemCtx.ctxAffPart
                      | Context.INT => OpSemCtx.ctxIntPart
    in
      solve (false, filterCtx ctx, G,
          fn (N, ctx') => solveList (consumeAll, ctx') gs (fn (Ns, ctxo) => sc ((* dummyObj *) N::Ns, ctxo)))
    end

(* matchAtom : bool * context * asyncType asyncTypeF * (obj * context -> unit) -> unit *)
(* Choice point: choose hypothesis and switch from Right Inversion to Left Focusing *)
and matchAtom (consumeAll, ctx, P, sc) =
    ( if !traceSolve >= 2 then
        print ("Subgoal: MatchAtom ("^PrettyPrint.printType (AsyncType.inj P)^")\n")
      else ()
    ; matchAtom' (consumeAll, ctx, P, sc) )
and matchAtom' (consumeAll, ctx, P, sc) =
    let
      val aP = (case P of TAtomic (a, _) => a
                        | _ => raise Fail "Internal error: wrong argument to matchAtom!")
      val P' = AsyncType.inj P
      fun lFocus (ctx', lr, A, h) = fn () =>
                                       ( traceLeftFocus (h, A)
                                       ; leftFocus (lr, consumeAll, ctx', P', A, fn (S, ctxo) =>
                                                                                    sc ((* dummyObj *) Atomic' (h, S), ctxo)) )
      fun matchSig (c, lr, A) = fn () => BackTrack.backtrack (lFocus (ctx, lr, A, Const c))
      fun matchCtx [] = []
        | matchCtx ((k, x, (A, hds), modality) :: t) =
          if hds = nil orelse #2 (List.hd hds) <> HdAtom(aP) andalso List.tl hds = nil
          then matchCtx t
          else
            let
              val A' = TClos (A, Subst.shift k)
              val h = Var (modality, k)
              val validHds = List.filter (fn (_, HdAtom a) => a=aP | _ => false) hds
              val candidates = List.map (fn (lr, _) => (fn () => BackTrack.backtrack (lFocus (OpSemCtx.removeHyp (ctx, k, modality), lr, A', h)))) validHds
            in
              candidates @ matchCtx t
            end
      val ctxlist = OpSemCtx.nonDepPart ctx
      val available = matchCtx ctxlist
    (*
     val ctxLength = List.length ctxlist
     val () = totalCtxLength := !totalCtxLength+ctxLength
     val availLength = List.length available
     val () = totalAvailLength := !totalAvailLength+availLength
     val () = TextIO.print (Int.toString (!totalCtxLength) ^ " -> " ^ Int.toString (!totalAvailLength)
                            ^ "\n")
     *)
    in
      (*
         Timers.time Timers.fairness (fn () => PermuteList.forAll (fn f => f ())
                                      (PermuteList.fromList (matchCtx (ctx2list $ #2 ctx, 1) @ map matchSig (getCandAtomic aP)))) ()
       *)
      PermuteList.forAll (fn f => f ())
                         (PermuteList.fromList (available @ map matchSig (getCandAtomic aP)))
    end

(* matchAtomEmpty : bool * context * asyncType asyncTypeF * (obj * context -> unit) -> unit *)
(* matches an atomic type of an empty family by just looking at the context *)
(* all arguments are negative, so we only have to match the spine *)
and matchAtomEmpty (consumeAll, ctx, P, sc) =
    ( if !traceSolve >= 2 then
        print ("Subgoal: MatchAtomEmpty ("^PrettyPrint.printType (AsyncType.inj P)^")\n")
      else ()
    ; matchAtomEmpty' (consumeAll, ctx, P, sc) )
and matchAtomEmpty' (consumeAll, ctx, P, sc) =
    let
      val (head, spine) = case P of
                            TAtomic (a, S) => (a, S)
                          | _ => raise Fail "Internal error: wrong argument to matchAtom!"
      val (spineIn, spineOut) = partitionArgs (head, spine)
      val () = if null spineIn then () else raise Fail "Internal error: empty families should have only outputs"

      fun tryHyp (A, h, k, modality) =
          case AsyncType.prj A of
            TAtomic (a, S) =>
            let
              val () = if a <> head then raise Fail "Internal error: family error" else ()
              val (Sin, Sout) = partitionArgs (a, S)
              val () = if null Sin then () else raise Fail "Internal error: empty families should have only outputs"
            in
              BackTrack.backtrack (fn () =>
              Match.matchList (spineOut, Sout) (fn () =>
                                         let
                                           val ctx' = OpSemCtx.removeHyp (ctx, k, modality)
                                         in
                                           if consumeAll
                                           then if OpSemCtx.nolin ctx'
                                                then sc ((* dummyObj *) Atomic' (h, Nil'), ctx')
                                                else ()
                                           else sc ((* dummyObj *) Atomic' (h, Nil'), ctx')
                                         end)
              )
            end
          | _ => raise Fail "Internal error: family not empty?"

      (* TODO: check the signature and additive conjunctions *)
      fun matchCtx [] = ()
        | matchCtx ((k, x, (A, [(_, HdAtom h)]), modality) :: t) =
          if head = h
          then
            let
              val A' = TClos (A, Subst.shift k)
              val h = Var (modality, k)
            in
              tryHyp (A', h, k, modality)
            ; matchCtx t
            end
          else matchCtx t
    in
      matchCtx (OpSemCtx.nonDepPart ctx)
    end
(* forwardStep : context
 *                -> (context *
 *                    whatever it is that nbinds returns *
 *                    (pattern * pattern's type * atomicterm)) option *)
and forwardStep (ctx : context) =
    let
      fun mlFocus (ctx', lr, A, h) =
       fn commitExn =>
          ( traceLeftFocus (h, A)
          ; monLeftFocus (lr, ctx', A,
                       fn (S, sty, ctxo) => raise commitExn ((h, S), sty, ctxo))
          )

      (* matchCtx and matchSig are going to give us the different ways of
       * trying to foward chain one step in the current context as functions
       * unit -> a term that can be derived, the synchronous type that
       * left-focusing on this term will dump into the context, and
       * presumably the new, modified context.
       *
       * Each of these candidate functions implement "if I try this rule,
       * what progress do I make in the current context?" The PermuteList
       * stuff allows us to then try all the possibilities in some
       * (unspecified) order. *)

      fun matchSig (c, lr, A) =
          let
            val gP = GoalPattern.getGoalPattern c
            val gpStr = case gP of
                          NONE => "(none)... "
                        | SOME (c, NONE) => "("^c^")... "
                        | SOME (c, SOME a) => "("^c^", "^a^")... "
            val () = if !traceSolve >= 2
                     then print ("checking goalPattern for "^c^gpStr)
                     else ()
            val b = matchCtxGoalPattern (ctx, gP)
          in
            if b
            then
              [ fn () => BackTrack.backtrackC (mlFocus (ctx, lr, A, Const c))]
            else []
          end

      fun matchCtx [] = []
        | matchCtx ((k, x, (A, hds), modality) :: t) =
          let
            val ctx' = OpSemCtx.removeHyp (ctx, k, modality)
            val A' = TClos (A, Subst.shift k)
          in
            List.mapPartial
              (fn (_, HdAtom _) => NONE
                | (lr, HdMonad) =>
                  SOME (fn () =>
                           BackTrack.backtrackC
                             (mlFocus (ctx', lr, A', Var (modality, k)))))
              hds
              @ matchCtx t
          end

      val candidates1 = matchCtx (OpSemCtx.nonDepPart ctx) (* Not needed if there are no forward-chaining embedded clauses *)
      val candidates2 = map matchSig (getCandMonad ())
      val candidates = candidates1 @ List.concat candidates2

      val () =
          if !debugForwardChaining
          then
            (* using #trace this context-printing is maybe no longer needed? *)
            (*print "Context: "
           ; printCtx (l, ctx) *)
            ( print (Int.toString (length candidates) ^ " candidates")
            ; if (length candidates1 > 0)
              then print (", " ^ Int.toString (length candidates2)
                          ^ " from the context. <press ENTER to continue>")
              else print (". <press ENTER to continue>")
            ; TextIO.flushOut TextIO.stdOut
            ; ignore (TextIO.inputLine TextIO.stdIn))
          else ()

    in
      case PermuteList.findSome (fn f => f ())
                                (PermuteList.fromList candidates) of
        NONE => NONE
      | SOME (N, sty, ctxm) =>
        let
          val p = syncType2pat sty
          val p' = Util.patternT2O p
        in
          SOME ((pushBind (p, sty) $ ctxm),
                nbinds p,
                (p', sty, N))
        end
    end


(* forwardChain : int option * int * (lcontext * context) * syncType * (expObj * context -> unit) -> unit *)
and forwardChain (fcLim, consumeAll, ctx, S, sc) =
    ( if !traceSolve >= 2
      then print ("ForwardChain ("^PrettyPrint.printType (TMonad' S)^")\n")
      else ()
    ; forwardChain' (fcLim, 0, consumeAll, ctx, S, sc) )

and forwardChain' (fcLim, currIter, consumeAll, ctx, S, sc) =
    let
      val () = TextIO.outputSubstr (TextIO.stdErr, Substring.full ("\rIteration: "^Int.toString currIter))
      val counter = ref 0
    in
      if fcLim = SOME 0
      then rightFocus (consumeAll, ctx, S,
                    fn (M, ctxo) => sc ((* dummyExpObj *) Mon' M, ctxo))
      else
        (case forwardStep ctx of
           NONE => rightFocus (consumeAll, ctx, S,
                            fn (M, ctxo) => sc ((* dummyExpObj *) Mon' M, ctxo))
         | SOME (newctx, newbinds, (p, sty, N)) =>
           let
             val () = if !traceSolve >= 1
                      then print ("Committing:\n   let {_} = "
                                  ^PrettyPrint.printObj (Atomic' N)
                                  ^" : {"^PrettyPrint.printSyncType sty^"}\n")
                      else ()
           in
             forwardChain' (Option.map (fn x => x - 1) fcLim,
                            currIter + 1,
                            consumeAll,
                            newctx,
                            STClos (S, Subst.shift $ newbinds),
                         fn (E, ctxo) =>
                            sc ((* dummyExpObj *) Let' (p, N, E), OpSemCtx.ctxPopNum (nbinds p) ctxo))
           end)
    end

(* rightFocus : bool * context * monadObj * syncType * (monadObj * context -> unit) -> unit *)
and rightFocus (consumeAll, ctx, sty, sc) =
    ( if !traceSolve >= 2 then
        print ("RightFocus ("^PrettyPrint.printType (TMonad' sty)^")\n")
      else ()
    ; rightFocus' (consumeAll, ctx, sty, sc) )
and rightFocus' (consumeAll, ctx, sty, sc) =
    let
      val (subgoals, mkMonadObj) = decomposeSync (ctx, sty)
      (* fun ppG [] = "" *)
      (*   | ppG (h :: t) = PrettyPrint.printType h ^ ", " ^ ppG t *)
      (* fun ppSG () = print ("Subgoals " ^ ppG subgoals ^ "\n") *)
      (* val () = (print ("RightFocus ("^PrettyPrint.printType (TMonad' sty)^")\n") *)
      (*         ; ppSG ()) *)
    in
      solveList (consumeAll, ctx) subgoals (fn (Ns, ctx') => sc ((* dummyMonadObj *) mkMonadObj Ns, ctx'))
    end
(* leftFocus : lr list * (lcontext * context) * asyncType * asyncType * (spine * context -> unit) -> unit *)
(* Left Focusing : Gamma;Delta;A >> P  ~~  leftFocus (LR-Oracle, Gamma;Delta, P, A, SuccCont)
 * Construct the spine corresponding to the chosen hypothesis. %%
*)
and leftFocus (lr, consumeAll, ctx : context, P, ty, sc) =
    ( if !traceSolve >= 3 then
        print ("LeftFocus ("^PrettyPrint.printType ty^")\n")
      else ()
    ; leftFocus' (lr, consumeAll, ctx, P, ty, sc) )
and leftFocus' (lr, consumeAll, ctx, P, ty, sc) =
    let
      val at = case Util.typePrjAbbrev P of
                 TAtomic (a, _) => a
               | _ => raise Fail "Internal leftFocus on non-atomic goal"
      val (Pin, Pout) = case Util.typePrjAbbrev P of
                          TAtomic (a, S) => partitionArgs (a, S)
                        | _ => raise Fail "Internal leftFocus on non-atomic goal2"
      val (Sin, subgoals, Sout, mkSpine) = decomposeAtomic (lr, ctx, ty)
      (* val _ = print ("Goal " ^PrettyPrint.printType P ^"\n") *)
      (* val _ = print ("Left Focus " ^PrettyPrint.printType ty ^"\n") *)
      fun ppIn () = () (* print ("+ " ^PrettyPrint.printType (TAtomic' (at, List.foldr TApp' TNil' Sin)) ^"\n") *)
      fun ppOut () = () (* print ("- " ^PrettyPrint.printType (TAtomic' (at, List.foldr TApp' TNil' Sout)) ^"\n") *)
      fun ppG [] = ""
        | ppG (h :: t) = PrettyPrint.printType h ^ ", " ^ ppG t
      fun ppSG () = () (* print ("Subgoals " ^ ppG subgoals ^ "\n") *)
      (* val _ = print "Matching inputs\n" *)
      (* val _ = Match.outputMatch := true *)
      fun matchList' obs1 obs2 sc = List.foldr (fn (ob, r) => fn () => Match.match ob r) sc (ListPair.zip (obs1, obs2))
      fun matchList obs1 obs2 sc = matchList' obs1 obs2 sc ()
    in
      (ppIn ();
       matchList Sin Pin (fn () => (ppSG ();
       solveList (consumeAll, ctx) subgoals (fn (Ns, ctx') => (ppOut ();
       matchList Pout Sout (fn () => (sc ((* dummySpine *) mkSpine Ns, ctx'))))))))
    (* TODO: check that no linear hyp are available after solving subgoals *)
    end
(* monLeftFocus : lr list * context * asyncType * (spine * syncType * context -> unit) -> unit *)
and monLeftFocus (lr, ctx, ty, sc) =
    ( if !traceSolve >= 3 then
        print ("monLeftFocus ("^PrettyPrint.printType ty^")\n")
      else ()
    ; monLeftFocus' (lr, ctx, ty, sc) )
and monLeftFocus' (lr, ctx, ty, sc) =
    let
      val (subgoals, mkSpine, sty) = decomposeMonadic (lr, ctx, ty)
      (* fun ppG [] = "" *)
      (*   | ppG (h :: t) = PrettyPrint.printType h ^ ", " ^ ppG t *)
      (* fun ppSG () = print ("Subgoals " ^ ppG subgoals ^ "\n") *)
      (* val _ = (ppSG (); print ("Monadic type: " ^ PrettyPrint.printSyncType sty ^"\n")) *)
    in
      solveList (false, ctx) subgoals (fn (Ns, ctx') =>
      sc ((* dummySpine *) mkSpine Ns, sty, ctx'))
    end

(* solveEC : asyncType * (obj -> unit) -> unit *)
fun solveEC (ty, sc) = solve (true, OpSemCtx.emptyCtx, ty, sc o #1)

fun trace printInter limit sty =
    let
      fun loop (context : context) count : int * (lcontext * context) =
          ( if printInter then (printCtx ([], context)) else ()
          ; if limit = SOME count then (count, (OpSemCtx.linearIndices context, context))
            else case forwardStep context of
                   NONE => (count, (OpSemCtx.linearIndices context, context))
                 | SOME (context', _, _) => loop context' (count+1))
    in
      loop (pushBind (syncType2pat sty, sty) OpSemCtx.emptyCtx) 0
    end

end
