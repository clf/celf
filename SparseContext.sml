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

structure Context :> CONTEXT =
struct

exception ExnCtx of string

datatype modality = INT | AFF | LIN
(* With sparse contexts there is no need of cmodality.
   Kept for backward compatibility *)
type cmodality = modality option

(* Each cell in the context contains its deBruijn index *)
type 'a localvar = int * string * 'a * modality

type 'a context = 'a localvar list

fun updatePos f (k, x, a, m) = (f k, x, a, m)
fun updateValue f (k, x, a, m) = (k, x, f a, m)

fun ctx2list ctx  =
    let
      fun trans n [] = []
        | trans n ((h as (k, x, a, m)) :: t) =
          case Int.compare (n, k) of
            LESS => ("_", a, NONE) :: trans (n+1) (h::t)
          | EQUAL => (x, a, SOME m) :: trans (n+1) t
          | GREATER => raise Fail "Internal error: invariant broke in ctx2list"
    in
      trans 1 ctx
    end


fun list2ctx old =
    let
      fun trans _ [] = []
        | trans k ((x, a, SOME m) :: t) = (k, x, a, m) :: trans (k+1) t
        | trans k ((_, _, NONE) :: t) = trans (k+1) t
    in
      trans 1 old
    end

fun ctxCons (_, _, NONE) ctx = ctx
  | ctxCons (x, a, SOME m) ctx = (1, x, a, m) :: List.map (updatePos (fn k => k+1)) ctx

fun ctxMap f ctx = List.map (updateValue f) ctx

fun ctxLength ctx = List.length ctx

val emptyCtx = []

fun ctxIntPart (ctx : 'a context) = List.filter (fn (_, _, _, m) => m=INT) ctx

fun ctxAffPart (ctx : 'a context) = List.filter (fn (_, _, _, m) => m=INT orelse m=AFF) ctx

(* ctxLookupNum : 'a context * int -> 'a context * modality * 'a *)
fun ctxLookupNum ([], n) = raise Fail "Internal error: accessing already consumed variable"
  | ctxLookupNum ((h as (k, x, a, m)) :: ctx, n) =
    if k = n then
      let
        val ctx' = if m = INT then h :: ctx else ctx
      in
        (ctx', m, a)
      end
    else
      let
        val (ctx', m, v) = ctxLookupNum (ctx, n)
      in
        (h :: ctx', m, v)
      end

(* ctxLookupName : 'a context * string -> (int * modality * 'a * 'a context) option *)
fun ctxLookupName ([], y) = NONE
  | ctxLookupName ((h as (k, x, a, m)) :: ctx, y) =
    if y = x then
      let
        val ctx' = if m = INT then h :: ctx else ctx
      in
        SOME (k, m, a, ctx')
      end
    else
      ( case ctxLookupName (ctx, y) of
          NONE => NONE
        | SOME (k', m', a', ctx') => SOME (k', m', a', h :: ctx')
      )

(* ctxPush : string * modality * 'a * 'a context -> 'a context *)
(* why ctxPush and ctxCons ? -jls *)
fun ctxPush (x, m, a, ctx) = (1, x, a, m) :: List.map (updatePos (fn k => k+1)) ctx

(* ctxPushNO : 'a * 'a context -> 'a context *)
fun ctxPushNO (_, ctx) = List.map (updatePos (fn k => k+1)) ctx

(* ctxCondPushINT : string option * 'a * 'a context -> 'a context *)
fun ctxCondPushINT (NONE, _, ctx) = ctx
  | ctxCondPushINT (SOME x, A, ctx) = ctxPush (x, INT, A, ctx)


(* remNeg : 'a context -> 'a context
   Removes elements whose #pos is < 1
   Assumes that positions are ordered
 *)
fun remNeg [] = []
  | remNeg (ctx as (k, _, _, _) :: t) = if k < 1 then remNeg t else ctx


(* nolin : 'a context -> 'a option *)
fun nolin (ctx : 'a context) = List.find (fn (_, _, _, m) => m = LIN) ctx

(* fun ctxAddJoin : context * context -> context *)
(* newCtxAddJoin (ctx1, ctx2) removes all affine hypotheses that appear in only one
   context. Fails if a linear variable appears in one but not the other *)
(* Assumes that both contexts are ordered *)
fun ctxAddJoin (ctx1, ctx2) =
    let
      fun joinerr x = "Contexts can't join: linear variable "^x^" only occurs on one side\n"
      fun checkNolin (ctx : 'a context) =
          case nolin ctx of
            NONE => ctx
          | SOME (_, x, _, _) => raise ExnCtx (joinerr x)
    in
      case (ctx1, ctx2) of
        ([], ctx2') => checkNolin ctx2'
      | (ctx1', []) => checkNolin ctx1'
      | ((h1 as (k1, x1, a1, m1)) :: t1, (k2, x2, a2, m2) :: t2) =>
        case Int.compare (k1, k2) of
          LESS => ( case m1 of
                      LIN => raise ExnCtx (joinerr x1)
                    | AFF => ctxAddJoin (t1, ctx2)
                    | INT => raise Fail "Internal error: INT on left side only (ctxAddJoin)"
                  )
        | EQUAL => ( if m1=m2 then () else raise Fail "Internal error: ctxAddJoin" (* sanity check *)
                   ; h1 :: ctxAddJoin (t1, t2)
                   )
        | GREATER => ( case m2 of
                         LIN => raise ExnCtx (joinerr x2)
                       | AFF => ctxAddJoin (ctx1, t2)
                       | INT => raise Fail "Internal error: INT on right side only (ctxAddJoin)"
                     )
    end


fun ctxJoinAffLin (ctx1, ctx2) =
    let
      (* remAff removes affine hypotheses from a context *)
      fun remAff [] = []
        | remAff ((h as (k, x, a, m)) :: t) =
          ( case m of
              LIN => h :: remAff t
            | AFF => remAff t
            | INT => raise Fail "Internal error: context misalignment (remAff)"
          )
      fun checkNolin (ctx : 'a context) =
          case nolin ctx of
            NONE => ctx
          | SOME _ => raise Fail "Internal error: context misalignment (ctxJoinAffLin)"
    in
      case (ctx1, ctx2) of
        ([], ctx2') => remAff ctx2'
      | (ctx1', []) => checkNolin ctx1'
      | (ctx1' as (h1 as (k1, x1, a1, m1)) :: t1, ctx2' as (h2 as (k2, x2, a2, m2)) :: t2) =>
        case Int.compare (k1, k2) of
          LESS => ( case m1 of
                      LIN => raise Fail "Internal error: ctxJoinAffLin 3"
                    | AFF => h1 :: ctxJoinAffLin (t1, ctx2')
                    | INT => raise Fail "Internal error: INT on left side only (ctxJoinAffLin)"
                  )
        | EQUAL => ( if m1=m2 then () else raise Fail "Internal error: ctxJoinAffLin 1" (* sanity check *)
                   ; case m1 of
                       LIN => raise Fail "Internal error: ctxJoinAffLin 2"
                     | _ (* AFF, INT *) => h1 :: ctxJoinAffLin (t1, t2)
                   )
        | GREATER => ( case m2 of
                         LIN => h2 :: ctxJoinAffLin (ctx1', t2)
                       | AFF => ctxJoinAffLin (ctx1', t2)
                       | INT => raise Fail "Internal error: INT on right side only (ctxJoinAffLin)"
                     )
    end


(* ctx2sparseList : 'a context -> (int * string * 'a * modality) list *)
fun ctx2sparseList ctx = ctx

fun sparseList2ctx xs = xs

(* ctxPushList : (string * modality * 'a) list -> 'a context -> 'a context *)
fun ctxPushList xs ctx =
    let
      fun mkList _ [] acc = acc
        | mkList k ((x, m, a) :: t) acc =
          mkList (k-1) t ((k, x, a, m) :: acc)
      val len = List.length xs
    in
      mkList len xs [] @ List.map (updatePos (fn k => k+len)) ctx
    end

(* ctxPopNum : int -> 'a context -> 'a context *)
fun ctxPopNum n ctx =
    let
      fun split [] = ([], [])
        | split ((h as (k, x, a, m)) :: t) =
          if k <= n then
            let
              val (ls, gs) = split t
            in
              (h :: ls, gs)
            end
          else
            ([], h :: t)
      val (ls, gs) = split ctx
    in
      case List.find (fn (_, _, _, m) => m = LIN) ls of
        SOME (_, x, _, _) => raise ExnCtx ("Linear variable "^x^" doesn't occur\n")
      | NONE => List.map (updatePos (fn k => k-n)) gs
    end

(* ctxPop : 'a context -> 'a context *)
fun ctxPop ctx = ctxPopNum 1 ctx

end
