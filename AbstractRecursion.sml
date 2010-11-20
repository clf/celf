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

(* This is based on Wang and Murphy's Programming with Recursion Schemes
 * (available from http://www-2.cs.cmu.edu/~tom7/papers).
 * It has been expanded to support mutually recursive datatypes.
 *)

signature TYP = sig
(* abstract type t *)
type t
(* public datatype 't F that reveals the
   constructors of the type t *)
type 't F
(* isomorphism t = t F *)
val inj : t F -> t
val prj : t -> t F
(* Fmap (fn x => x) == (fn x => x)
   Fmap (f o g) == (Fmap f) o (Fmap g) *)
val Fmap : ('t1 -> 't2) -> 't1 F -> 't2 F
end

signature TYP2 = sig
type a
type t
type ('a, 't) F
val inj : (a, t) F -> t
val prj : t -> (a, t) F
val Fmap : ('a1 -> 'a2) * ('t1 -> 't2) -> ('a1, 't1) F -> ('a2, 't2) F
end

signature TYP3 = sig
type a
type b
type t
type ('a, 'b, 't) F
val inj : (a, b, t) F -> t
val prj : t -> (a, b, t) F
val Fmap : (('a1 -> 'a2) * ('b1 -> 'b2)) * ('t1 -> 't2) -> ('a1, 'b1, 't1) F -> ('a2, 'b2, 't2) F
end

signature TYP4 = sig
type a
type b
type c
type t
type ('a, 'b, 'c, 't) F
val inj : (a, b, c, t) F -> t
val prj : t -> (a, b, c, t) F
val Fmap : (('a1 -> 'a2) * ('b1 -> 'b2) * ('c1 -> 'c2)) * ('t1 -> 't2)
		-> ('a1, 'b1, 'c1, 't1) F -> ('a2, 'b2, 'c2, 't2) F
end

signature REC = sig
structure T : TYP
val fold : ('a T.F -> 'a) -> T.t -> 'a
val unfold : ('a -> 'a T.F) -> 'a -> T.t
val postorderMap : (T.t T.F -> T.t T.F) -> T.t -> T.t
val preorderMap : (T.t T.F -> T.t T.F) -> T.t -> T.t
end

signature REC2 = sig
structure T : TYP2
val Fmap1 : ('a1 -> 'a2) -> ('a1, 't) T.F -> ('a2, 't) T.F
val Fmapt : ('t1 -> 't2) -> ('a, 't1) T.F -> ('a, 't2) T.F
val fold : (T.a -> 'a) -> (('a, 't) T.F -> 't) -> T.t -> 't
val unfold : ('a -> T.a) -> ('t -> ('a, 't) T.F) -> 't -> T.t
val map : (T.a -> T.a) -> T.t -> T.t
val refold : ('ai -> 'ao) -> ('ti -> ('ai, 'ti) T.F) -> (('ao, 'to) T.F -> 'to) -> 'ti -> 'to
end

signature REC3 = sig
structure T : TYP3
val Fmap1 : ('a1 -> 'a2) -> ('a1, 'b, 't) T.F -> ('a2, 'b, 't) T.F
val Fmap2 : ('b1 -> 'b2) -> ('a, 'b1, 't) T.F -> ('a, 'b2, 't) T.F
val Fmapt : ('t1 -> 't2) -> ('a, 'b, 't1) T.F -> ('a, 'b, 't2) T.F
val fold : (T.a -> 'a) * (T.b -> 'b) -> (('a, 'b, 't) T.F -> 't) -> T.t -> 't
val unfold : ('a -> T.a) * ('b -> T.b) -> ('t -> ('a, 'b, 't) T.F) -> 't -> T.t
val map : (T.a -> T.a) * (T.b -> T.b) -> T.t -> T.t
val refold : ('ai -> 'ao) * ('bi -> 'bo) ->
	('ti -> ('ai, 'bi, 'ti) T.F) -> (('ao, 'bo, 'to) T.F -> 'to) -> 'ti -> 'to
end

signature REC4 = sig
structure T : TYP4
val Fmap1 : ('a1 -> 'a2) -> ('a1, 'b, 'c, 't) T.F -> ('a2, 'b, 'c, 't) T.F
val Fmap2 : ('b1 -> 'b2) -> ('a, 'b1, 'c, 't) T.F -> ('a, 'b2, 'c, 't) T.F
val Fmap3 : ('c1 -> 'c2) -> ('a, 'b, 'c1, 't) T.F -> ('a, 'b, 'c2, 't) T.F
val Fmapt : ('t1 -> 't2) -> ('a, 'b, 'c, 't1) T.F -> ('a, 'b, 'c, 't2) T.F
val fold : (T.a -> 'a) * (T.b -> 'b) * (T.c -> 'c) -> (('a, 'b, 'c, 't) T.F -> 't) -> T.t -> 't
val unfold : ('a -> T.a) * ('b -> T.b) * ('c -> T.c) -> ('t -> ('a, 'b, 'c, 't) T.F) -> 't -> T.t
val map : (T.a -> T.a) * (T.b -> T.b) * (T.c -> T.c) -> T.t -> T.t
val refold : ('ai -> 'ao) * ('bi -> 'bo) * ('ci -> 'co) ->
	('ti -> ('ai, 'bi, 'ci, 'ti) T.F) -> (('ao, 'bo, 'co, 'to) T.F -> 'to) -> 'ti -> 'to
end

functor Rec(structure T : TYP) : REC = struct
structure T = T
open T
fun wrapF f g h x = f (Fmap h (g x))
fun fold step x = wrapF step prj (fold step) x
fun unfold gen y = wrapF inj gen (unfold gen) y
fun postorderMap f v = fold (inj o f) v
fun preorderMap f v = unfold (f o prj) v
end

functor Rec2(structure T : TYP2) : REC2 = struct
structure T = T
open T
fun Fmap1 f = T.Fmap (f, fn x=>x)
fun Fmapt f = T.Fmap (fn x=>x, f)
fun fold f step x = step (Fmap (f, fold f step) (prj x))
fun unfold f gen y = inj (Fmap (f, unfold f gen) (gen y))
fun map f x = inj (Fmap (f, map f) (prj x))
fun refold f gen step x = step (Fmap (f, refold f gen step) (gen x))
end

functor Rec3(structure T : TYP3) : REC3 = struct
structure T = T
open T
fun Fmap1 f = T.Fmap ((f, fn x=>x), fn x=>x)
fun Fmap2 f = T.Fmap ((fn x=>x, f), fn x=>x)
fun Fmapt f = T.Fmap ((fn x=>x, fn x=>x), f)
fun fold f step x = step (Fmap (f, fold f step) (prj x))
fun unfold f gen y = inj (Fmap (f, unfold f gen) (gen y))
fun map f x = inj (Fmap (f, map f) (prj x))
fun refold f gen step x = step (Fmap (f, refold f gen step) (gen x))
end

functor Rec4(structure T : TYP4) : REC4 = struct
structure T = T
open T
fun Fmap1 f = T.Fmap ((f, fn x=>x, fn x=>x), fn x=>x)
fun Fmap2 f = T.Fmap ((fn x=>x, f, fn x=>x), fn x=>x)
fun Fmap3 f = T.Fmap ((fn x=>x, fn x=>x, f), fn x=>x)
fun Fmapt f = T.Fmap ((fn x=>x, fn x=>x, fn x=>x), f)
fun fold f step x = step (Fmap (f, fold f step) (prj x))
fun unfold f gen y = inj (Fmap (f, unfold f gen) (gen y))
fun map f x = inj (Fmap (f, map f) (prj x))
fun refold f gen step x = step (Fmap (f, refold f gen step) (gen x))
end

functor Typ1From2(structure T : TYP2) : TYP = struct
type t = T.t
type 't F = (T.a, 't) T.F
val inj = T.inj
val prj = T.prj
fun Fmap f = T.Fmap (fn x=>x, f)
end

functor Typ1From3(structure T : TYP3) : TYP = struct
type t = T.t
type 't F = (T.a, T.b, 't) T.F
val inj = T.inj
val prj = T.prj
fun Fmap f = T.Fmap ((fn x=>x, fn x=>x), f)
end

functor Typ1From4(structure T : TYP4) : TYP = struct
type t = T.t
type 't F = (T.a, T.b, T.c, 't) T.F
val inj = T.inj
val prj = T.prj
fun Fmap f = T.Fmap ((fn x=>x, fn x=>x, fn x=>x), f)
end

functor Injs(structure T : TYP) = struct
open T
fun inj_succ inj_pred x = inj (Fmap inj_pred x)
val inj1 = inj
val inj2 = inj_succ inj1
val inj3 = inj_succ inj2
val inj4 = inj_succ inj3
val inj5 = inj_succ inj4
end
functor Prjs(structure T : TYP) =
struct
open T
fun prj_succ prj_pred x = Fmap prj_pred (prj x)
val prj1 = prj
val prj2 = prj_succ prj1
val prj3 = prj_succ prj2
val prj4 = prj_succ prj3
val prj5 = prj_succ prj4
end

signature AUX_DEFS = sig
structure T : TYP
val inj1 : T.t T.F -> T.t
val inj2 : T.t T.F T.F -> T.t
val inj3 : T.t T.F T.F T.F -> T.t
val inj4 : T.t T.F T.F T.F T.F -> T.t
val inj5 : T.t T.F T.F T.F T.F T.F -> T.t
val inj_succ : ('a -> T.t) -> 'a T.F -> T.t
val prj1 : T.t -> T.t T.F
val prj2 : T.t -> T.t T.F T.F
val prj3 : T.t -> T.t T.F T.F T.F
val prj4 : T.t -> T.t T.F T.F T.F T.F
val prj5 : T.t -> T.t T.F T.F T.F T.F T.F
val prj_succ : (T.t -> 'a) -> T.t -> 'a T.F
val fold : ('a T.F -> 'a) -> T.t -> 'a
val unfold : ('a -> 'a T.F) -> 'a -> T.t
end

functor AuxDefs(structure T : TYP) : AUX_DEFS = struct
structure T = T
structure Injs = Injs(structure T = T)
structure Prjs = Prjs(structure T = T)
structure Rec = Rec(structure T = T)
open Injs Prjs Rec
end

