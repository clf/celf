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

structure OpSemCtx :> OPSEMCTX =
struct

exception ExnCtx of string

(* Each cell in the context contains its deBruijn index *)
type 'a localvar = int * string * 'a * Context.modality

(* A context is composed of four lists:
 * - linear part (all names ""),
 * - affine part (all names ""),
 * - non-dependent intuitionistic part (all names ""),
 * - dependent intuitionistic part (real names)
 * Internal invariant: each list is ordered by index *)
type 'a context = 'a localvar list * 'a localvar list * 'a localvar list * 'a localvar list

fun updatePos f (k, x, a, m) = (f k, x, a, m)
fun updateValue f (k, x, a, m) = (k, x, f a, m)
fun getPos (k, _, _, _) = k
fun getName (_, x, _, _) = x

fun shiftPos n xs = List.map (updatePos (fn k => k+n)) xs

(* mergeLVlist : 'a localvar list * 'a localvar list -> 'a localvar list *)
fun mergeLVlist ([], ys) = ys
  | mergeLVlist (xs, []) = xs
  | mergeLVlist ((k1, x1, a1, m1) :: xs, (k2, x2, a2, m2) :: ys) =
    ( case Int.compare (k1, k2) of
        LESS => (k1, x1, a1, m1) :: mergeLVlist (xs, (k2, x2, a2, m2) :: ys)
      | EQUAL => raise Fail "Internal error: invariant broke in mergeLVlist"
      | GREATER => (k2, x2, a2, m2) :: mergeLVlist ((k1, x1, a1, m1) :: xs, ys)
    )

(* unifyCtx makes one big list merging all parts of the context *)
fun unifyCtx (lvLin, lvAff, lvNd, lvDep) =
    List.foldl mergeLVlist [] [lvLin, lvAff, lvNd, lvDep]

(* splitCtx is the inverse of unifyCtx.
 * Puts all (_, NONE, _, Context.INT) in the non-dependent part and
 *      all (_, SOME _, _, Context.INT) in the dependent part. *)
fun splitCtx [] = ([], [], [], [])
  | splitCtx ((k, x, a, m) :: ctx) =
    let
      val (lvLin, lvAff, lvNd, lvDep) = splitCtx ctx
    in
      case m of
        Context.LIN => ((k, x, a, m) :: lvLin, lvAff, lvNd, lvDep)
      | Context.AFF => (lvLin, (k, x, a, m) :: lvAff, lvNd, lvDep)
      | Context.INT => if x=""
                       then (lvLin, lvAff, (k, x, a, m) :: lvNd, lvDep)
                       else (lvLin, lvAff, lvNd, (k, x, a, m) :: lvDep)
    end

(* findNonDep : (int * string * 'a * Context.modality -> bool) -> 'a context
                -> (int * string * 'a * Context.modality) option *)
fun findNonDep f (lvLin, lvAff, lvNd, _) =
    case List.find f lvLin of
      x as SOME _ => x
    | NONE => ( case List.find f lvAff of
                  x as SOME _ => x
                | NONE => ( case List.find f lvNd of
                              x as SOME _ => x
                            | NONE => NONE ))



fun ctx2list ctx =
    let
      fun trans n [] = []
        | trans n ((h as (k, x, a, m)) :: t) =
          case Int.compare (n, k) of
            LESS => ("_", a, NONE) :: trans (n+1) (h::t)
          | EQUAL => (x, a, SOME m) :: trans (n+1) t
          | GREATER => raise Fail "Internal error: invariant broke in ctx2list"
    in
      trans 1 (unifyCtx ctx)
    end


fun list2ctx old =
    let
      fun trans _ [] = ([], [], [], [])
        | trans k ((x, a, SOME m) :: t) =
          let
            val (lvLin, lvAff, lvNd, lvDep) = trans (k+1) t
          in
            case m of
              Context.LIN => ((k, SOME x, a, m) :: lvLin, lvAff, lvNd, lvDep)
            | Context.AFF => (lvLin, (k, SOME x, a, m) ::lvAff, lvNd, lvDep)
            | Context.INT => if x = ""
                     then (lvLin, lvAff, (k, NONE, a, m) :: lvNd, lvDep)
                     else  (lvLin, lvAff, lvNd, (k, SOME x, a, m) :: lvDep)
          end
        | trans k ((_, _, NONE) :: t) = trans (k+1) t
    in
      trans 1 old
    end

(* ctxCons : (string * 'a * Context.modality) -> 'a context -> 'a context *)
fun ctxCons (_, _, NONE) ctx = ctx
  | ctxCons (x, a, SOME m) (lvLin, lvAff, lvNd, lvDep) =
    let
      val lvLin' = shiftPos 1 lvLin
      val lvAff' = shiftPos 1 lvAff
      val lvNd' = shiftPos 1 lvNd
      val lvDep' = shiftPos 1 lvDep
    in
      case m of
        Context.LIN => ((1, SOME x, a, m) :: lvLin', lvAff', lvNd', lvDep')
      | Context.AFF => (lvLin', (1, SOME x, a, m) :: lvAff', lvNd', lvDep')
      | Context.INT => if x = ""
               then (lvLin', lvAff', (1, NONE, a, m) :: lvNd', lvDep')
               else (lvLin', lvAff', lvNd', (1, SOME x, a, m) :: lvDep')
    end

fun ctxLength (lvLin, lvAff, lvNd, lvDep) =
    List.length lvLin +
    List.length lvAff +
    List.length lvNd +
    List.length lvDep


val emptyCtx = ([], [], [], [])

fun ctxIntPart (_, _, lvNd, lvDep) = ([], [], lvNd, lvDep)

fun ctxAffPart (_, lvAff, lvNd, lvDep) = ([], lvAff, lvNd, lvDep)

(* removeHyp : 'a context * int * Context.modality -> 'a context *)
fun removeHyp ((ctx as (lvLin, lvAff, lvNd, lvDep)), n, m) =
    let
      fun lookupNum ([], n) = raise Fail "Internal error: accessing already consumed variable"
        | lookupNum ((h as (k, x, a, m)) :: ctx, n) =
          case Int.compare (k, n) of
            LESS => h :: lookupNum (ctx, n)
          | EQUAL => ctx
          | GREATER => h :: ctx
    in
    (*   print ("removeHyp "^Int.toString n^" from "^Int.toString (List.length lvLin) *)
    (*          ^", "^Int.toString (List.length lvAff) *)
    (*          ^", "^Int.toString (List.length lvNd) *)
    (*          ^", "^Int.toString (List.length lvDep) *)
    (*          ^ "\n") *)
    (* ; *) case m of
        Context.LIN => (lookupNum (lvLin, n), lvAff, lvNd, lvDep)
      | Context.AFF => (lvLin, lookupNum (lvAff, n), lvNd, lvDep)
      | _ => ctx
    end


(* ctxPush : string * Context.modality * 'a * 'a context -> 'a context *)
(* why ctxPush and ctxCons ? -jls *)
fun ctxPush (x, m, a, (lvLin, lvAff, lvNd, lvDep)) =
    let
      val lvLin' = shiftPos 1 lvLin
      val lvAff' = shiftPos 1 lvAff
      val lvNd' = shiftPos 1 lvNd
      val lvDep' = shiftPos 1 lvDep
    in
      case m of
        Context.LIN => ((1, x, a, m) :: lvLin', lvAff', lvNd', lvDep')
      | Context.AFF => (lvLin', (1, x, a, m) :: lvAff', lvNd', lvDep')
      | Context.INT => if x = ""
                       then (lvLin', lvAff', (1, "", a, m) :: lvNd', lvDep')
                       else (lvLin', lvAff', lvNd', (1, x, a, m) :: lvDep')
    end


(* remNeg : 'a context -> 'a context
   Removes elements whose #pos is < 1
   Assumes that positions are ordered
 *)
fun remNeg (lvLin, lvAff, lvNd, lvDep) =
    let
      fun rem [] = []
        | rem (ctx as (k, _, _, _) :: t) = if k < 1 then rem t else ctx
    in
      (rem lvLin, rem lvAff, rem lvNd, rem lvDep)
    end



(* fun ctxAddJoin : context * context -> context *)
(* newCtxAddJoin (ctx1, ctx2) removes all affine hypotheses that appear in only one
   context. Fails if a linear variable appears in one but not the other *)
(* Assumes that both contexts are ordered *)
fun ctxAddJoin ((lvLin1, lvAff1, lvNd, lvDep), (lvLin2, lvAff2, _, _)) =
    let
      fun joinerr x = "Contexts can't join: linear variable "^x^" only occurs on one side\n"
      fun intersect ([], ctx2) = ctx2
        | intersect (ctx1, []) = ctx1
        | intersect ((h1 as (k1, x1, a1, m1)) :: t1, (k2, x2, a2, m2) :: t2) =
          case Int.compare (k1, k2) of
            LESS => intersect (t1, (k2, x2, a2, m2) :: t2)
          | EQUAL => (k1, x1, a1, m1) :: intersect (t1, t2)
          | GREATER => intersect ((k1, x1, a1, m1) :: t1, t2)
      fun compare ([], []) = NONE
        | compare ((k, x, a, m) :: _, []) = SOME x
        | compare ([], (k, x, a, m) :: _) = SOME x
        | compare ((h1 as (k1, x1, a1, m1)) :: t1, (k2, x2, a2, m2) :: t2) =
          case Int.compare (k1, k2) of
            LESS => SOME x1
          | EQUAL => compare (t1, t2)
          | GREATER => SOME x2
    in
      case compare (lvLin1, lvLin2) of
        NONE => (lvLin1, intersect (lvAff1, lvAff2), lvNd, lvDep)
      | SOME x => raise ExnCtx (joinerr x)
    end


fun ctxJoinAffLin (ctx1, ctx2) =
    let
      fun ctxJoin (ctx1, ctx2) =
          let
            (* remAff removes affine hypotheses from a context *)
            fun remAff [] = []
              | remAff ((h as (k, x, a, m)) :: t) =
                ( case m of
                    Context.LIN => h :: remAff t
                  | Context.AFF => remAff t
                  | Context.INT => raise Fail "Internal error: context misalignment (remAff)"
                )
            (* nolin : 'a context -> 'a option *)
            val nolin = List.find (fn (_, _, _, m) => m = Context.LIN)
            fun checkNolin ctx =
                case nolin ctx of
                  NONE => ctx
                | SOME _ => raise Fail "Internal error: context misalignment (ctxJoin)"
          in
            case (ctx1, ctx2) of
              ([], ctx2') => remAff ctx2'
            | (ctx1', []) => checkNolin ctx1'
            | (ctx1' as (h1 as (k1, x1, a1, m1)) :: t1, ctx2' as (h2 as (k2, x2, a2, m2)) :: t2) =>
              case Int.compare (k1, k2) of
                LESS => ( case m1 of
                            Context.LIN => raise Fail "Internal error: ctxJoin 3"
                          | Context.AFF => h1 :: ctxJoin (t1, ctx2')
                          | Context.INT => raise Fail "Internal error: Context.INT on left side only (ctxJoin)"
                        )
              | EQUAL => ( if m1=m2 then () else raise Fail "Internal error: ctxJoin 1" (* sanity check *)
                         ; case m1 of
                             Context.LIN => raise Fail "Internal error: ctxJoin 2"
                           | _ (* Context.AFF, Context.INT *) => h1 :: ctxJoin (t1, t2)
                         )
              | GREATER => ( case m2 of
                               Context.LIN => h2 :: ctxJoin (ctx1', t2)
                             | Context.AFF => ctxJoin (ctx1', t2)
                             | Context.INT => raise Fail "Internal error: Context.INT on right side only (ctxJoin)"
                           )
          end
    in
      splitCtx (ctxJoin (unifyCtx ctx1, unifyCtx ctx2))
    end


(* ctx2sparseList : 'a context -> (int * string * 'a * Context.modality) list *)
fun ctx2sparseList ctx = unifyCtx ctx

fun linear2sparseList (lvLin, _, _, _) = lvLin

fun depPart (_, _, _, lvDep) = lvDep

fun nonDepPart (lvLin, lvAff, lvNd, lvDep) = lvNd @ lvAff @ lvLin

fun sparseList2ctx ctx =
    let
      fun addName (k, x, a, m) =
          case m of
            Context.INT => (k, x, a, m)
          | _  => (k, x, a, m)
    in
      splitCtx (List.map addName ctx)
    end

(* ctxPushList : (string * Context.modality * 'a) list -> 'a context -> 'a context *)
fun ctxPushList xs (lvLin, lvAff, lvNd, lvDep) =
    let
      fun mkList _ [] acc = acc
        | mkList k ((x, m, a) :: t) (acc as (lvLin, lvAff, lvNd, lvDep)) =
          ( case m of
              Context.LIN => mkList (k-1) t ((k, x, a, m) :: lvLin, lvAff, lvNd, lvDep)
            | Context.AFF => mkList (k-1) t (lvLin, (k, x, a, m) :: lvAff, lvNd, lvDep)
            | Context.INT => if x=""
                     then mkList (k-1) t (lvLin, lvAff, (k, "", a, m) :: lvNd, lvDep)
                     else mkList (k-1) t (lvLin, lvAff, lvNd, (k, x, a, m) :: lvDep)
          )
      val len = List.length xs
      val (lvLin', lvAff', lvNd', lvDep') = mkList len xs emptyCtx
      val lvLin2 = shiftPos len lvLin
      val lvAff2 = shiftPos len lvAff
      val lvNd2 = shiftPos len lvNd
      val lvDep2 = shiftPos len lvDep
    in
      (lvLin' @ lvLin2, lvAff' @ lvAff2, lvNd' @ lvNd2, lvDep' @ lvDep2)
    end

(* ctxPopNum : int -> 'a context -> 'a context *)
fun ctxPopNum n ((lvLin, lvAff, lvNd, lvDep) : 'a context) : 'a context =
    let
      val lvLin' = shiftPos (0-n) lvLin
      val lvAff' = shiftPos (0-n) lvAff
      val lvNd' = shiftPos (0-n) lvNd
      val lvDep' = shiftPos (0-n) lvDep
      val allLin = null lvLin' orelse getPos (List.hd lvLin') >= 0
    in
      if allLin
      then remNeg (lvLin', lvAff', lvNd', lvDep')
      else raise ExnCtx ("Linear variable "^getName (List.hd lvLin')^" doesn't occur\n")
    end

(* ctxPop : 'a context -> 'a context *)
fun ctxPop ctx = ctxPopNum 1 ctx

fun affIntersect ((lvLin, lvAff1, lvNd, lvDep),(_, lvAff2, _, _)) =
    let
      fun inter ([], _) = []
        | inter (_, []) = []
        | inter ((k1, x1, a1, m1) :: t1, (k2, x2, a2, m2) :: t2) =
          case Int.compare (k1, k2) of
            LESS => inter (t1, (k2, x2, a2, m2) :: t2)
          | EQUAL => (k1, x1, a1, m1) :: inter (t1, t2)
          | GREATER => inter ((k1, x1, a1, m1) :: t1, t2)
    in
      (lvLin, inter (lvAff1, lvAff2), lvNd, lvDep)
    end

fun linearDiff ((lvLin1, lvAff, lvNd, lvDep),(lvLin2, _, _, _)) =
    let
      fun linDiff ([], _) = []
        | linDiff (_, []) = []
        | linDiff ((k1, x1, a1, m1) :: t1, (k2, x2, a2, m2) :: t2) =
          case Int.compare (k1, k2) of
            LESS => (k1, x1, a1, m1) :: linDiff (t1, (k2, x2, a2, m2) :: t2)
          | EQUAL => linDiff (t1, t2)
          | GREATER => raise Fail "Internal error: linearDiff"
    in
      (linDiff (lvLin1, lvLin2), lvAff, lvNd, lvDep)
    end

fun nolin (lvLin, _, _, _) = null lvLin

fun linearIndices (lvLin, _, _, _) = List.map getPos lvLin

end
