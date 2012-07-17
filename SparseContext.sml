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
type 'a localvar = { pos: int
                   , name: string
                   , md: modality
                   , value: 'a }

type 'a context = 'a localvar list

fun withPos ({pos = _, name, md, value}, k) = { pos = k
                                              , name = name
                                              , md = md
                                              , value = value
                                              }
infix withPos

fun withValue ({pos, name, md, value = _}, v) = { pos = pos
                                                , name = name
                                                , md = md
                                                , value = v
                                                }
infix withValue

fun ctx2list ctx  =
    let
      fun trans n [] = []
        | trans n ((h : 'a localvar) :: t) =
          if n < #pos h
          then ("_", #value h, NONE) :: trans (n+1) (h::t)
          else if n = #pos h
          then (#name h, #value h, SOME (#md h)) :: trans (n+1) t
          else raise Fail "Internal error: invariant broke in ctx2list"
    in
      trans 1 ctx
    end


fun list2ctx old =
    let
      fun trans _ [] = []
        | trans k ((x, a, SOME m) :: t) =
          { pos = k
          , name = x
          , md = m
          , value = a } :: trans (k+1) t
        | trans k ((_, _, NONE) :: t) = trans (k+1) t
    in
      trans 1 old
    end

fun ctxCons (_, _, NONE) ctx = ctx
  | ctxCons (x, a, SOME m) ctx =
    { pos = 1
    , name = x
    , md = m
    , value = a
    } :: List.map (fn x => x withPos (#pos x + 1)) ctx

fun ctxMap f ctx =
    let
      fun appF c = c withValue f (#value c)
    in
      List.map appF ctx
    end

fun ctxLength ctx = List.length ctx

val emptyCtx = []

fun ctxIntPart (ctx : 'a context) = List.filter (fn x => #md x = INT) ctx

fun ctxAffPart (ctx : 'a context) = List.filter (fn x => #md x = INT orelse #md x = AFF) ctx

(* ctxLookupNum : 'a context * int -> 'a context * modality * 'a *)
fun ctxLookupNum ([], n) = raise Fail "Internal error: accessing already consumed variable"
  | ctxLookupNum ((h : 'a localvar) :: ctx, n) =
    if #pos h = n then
      let
        val ctx' = if #md h = INT then h :: ctx else ctx
      in
        (ctx', #md h, #value h)
      end
    else
      let
        val (ctx', m, v) = ctxLookupNum (ctx, n)
      in
        (h :: ctx', m, v)
      end

(* ctxLookupName : 'a context * string -> (int * modality * 'a * 'a context) option *)
fun ctxLookupName ([], x) = NONE
  | ctxLookupName ((h : 'a localvar) :: ctx, x) =
    if #name h = x then
      let
        val ctx' = if #md h = INT then h :: ctx else ctx
      in
        SOME (#pos h, #md h, #value h, ctx')
      end
    else
      ( case ctxLookupName (ctx, x) of
          NONE => NONE
        | SOME (n, m, v, ctx') => SOME (n, m, v, h :: ctx')
      )

(* ctxPush : string * modality * 'a * 'a context -> 'a context *)
(* why ctxPush and ctxCons ? -jls *)
fun ctxPush (x, m, a, ctx) = { pos = 1
                             , name = x
                             , md = m
                             , value = a
                             } :: List.map (fn x => x withPos (#pos x + 1)) ctx

(* ctxPushNO : 'a * 'a context -> 'a context *)
fun ctxPushNO (A, ctx) = List.map (fn x => x withPos (#pos x + 1)) ctx

(* ctxCondPushINT : string option * 'a * 'a context -> 'a context *)
fun ctxCondPushINT (NONE, _, ctx) = ctx
  | ctxCondPushINT (SOME x, A, ctx) = ctxPush (x, INT, A, ctx)


(* remNeg : 'a context -> 'a context
   Removes elements whose #pos is < 1
   Assumes that positions are ordered
 *)
fun remNeg [] = []
  | remNeg (ctx as (h : 'a localvar) :: t) = if #pos h < 1 then remNeg t else ctx


(* nolin : 'a context -> 'a option *)
fun nolin (ctx : 'a context) = List.find (fn x => #md x = LIN) ctx

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
          | SOME x => raise ExnCtx (joinerr (#name x))
    in
      case (ctx1, ctx2) of
        ([], ctx2') => checkNolin ctx2'
      | (ctx1', []) => checkNolin ctx1'
      | (h1 :: t1, h2 :: t2) =>
        if #pos h1 = #pos h2 then
          ( if #md h1 = #md h2 then () else raise Fail "Internal error: ctxAddJoin" (* sanity check *)
          ; h1 :: ctxAddJoin (t1, t2)
          )
        else
          if #pos h1 < #pos h2 then
            ( case #md h1 of
                LIN => raise ExnCtx (joinerr (#name h1))
              | AFF => ctxAddJoin (t1, ctx2)
              | INT => raise Fail "Internal error: INT on left side only (ctxAddJoin)"
            )
          else
            ( case #md h2 of
                LIN => raise ExnCtx (joinerr (#name h2))
              | AFF => ctxAddJoin (ctx1, t2)
              | INT => raise Fail "Internal error: INT on right side only (ctxAddJoin)"
            )
    end


fun ctxJoinAffLin (ctx1, ctx2) =
    let
      (* remAff removes affine hypotheses from a context *)
      fun remAff [] = []
        | remAff ((h : 'a localvar) :: t) =
          ( case #md h of
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
      | (ctx1' as h1 :: t1, ctx2' as h2 :: t2) =>
        if #pos h1 = #pos h2 then
          ( if #md h1 = #md h2 then () else raise Fail "Internal error: ctxJoinAffLin 1" (* sanity check *)
          ; case #md h1 of
              LIN => raise Fail "Internal error: ctxJoinAffLin 2"
            | _ (* AFF, INT *) => h1 :: ctxJoinAffLin (t1, t2)
          )
        else
          if #pos h1 < #pos h2 then
            (case #md h1 of
               LIN => raise Fail "Internal error: ctxJoinAffLin 3"
             | AFF => h1 :: ctxJoinAffLin (t1, ctx2')
             | INT => raise Fail "Internal error: INT on left side only (ctxJoinAffLin)"
            )
          else
            (case #md h2 of
               LIN => h2 :: ctxJoinAffLin (ctx1', t2)
             | AFF => ctxJoinAffLin (ctx1', t2)
             | INT => raise Fail "Internal error: INT on right side only (ctxJoinAffLin)"
            )
    end


(* ctx2sparseList : 'a context -> (int * string * 'a * modality) list *)
fun ctx2sparseList ctx = List.map (fn x : 'a localvar => (#pos x, #name x, #value x, #md x)) ctx

fun sparseList2ctx xs : 'a context =
    List.map (fn (n, x, a, m) => { pos = n, name = x, value = a, md = m }) xs

(* ctxPushList : (string * modality * 'a) list -> 'a context -> 'a context *)
fun ctxPushList xs ctx =
    let
      fun mkList _ [] acc = acc
        | mkList k ((x, m, a) :: t) acc =
          mkList (k-1) t ({ pos = k, name = x, value = a, md = m } :: acc)
      val len = List.length xs
    in
      mkList len xs [] @ List.map (fn x => x withPos (#pos x + len)) ctx
    end

(* ctxPopNum : int -> 'a context -> 'a context *)
fun ctxPopNum n ctx =
    let
      fun split [] = ([], [])
        | split ((h : 'a localvar) :: t) =
          if #pos h <= n then
            let
              val (ls, gs) = split t
            in
              (h :: ls, gs)
            end
          else
            ([], h :: t)
      val (ls, gs) = split ctx
    in
      case List.find (fn x : 'a localvar => #md x = LIN) ls of
        SOME x => raise ExnCtx ("Linear variable "^(#name x)^" doesn't occur\n")
      | NONE => List.map (fn x => x withPos (#pos x - n)) gs
    end

(* ctxPop : 'a context -> 'a context *)
fun ctxPop ctx = ctxPopNum 1 ctx

end
