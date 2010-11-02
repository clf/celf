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

signature NATSET =
sig

exception ExnNatSet

(* sets of natural numbers *)
type natset

(* val empty = [] *)
val empty : natset

(* fun isEmpty ns = ns = [] *)
val isEmpty : natset -> bool

(* fun singleton n = if n >= 1 then [n] else raise ExnNatSet *)
val singleton : int -> natset

(* fun decrn n ns = List.filter (fn x => x>=1) (map (fn x => x-n) ns) *)
val decrn : int -> natset -> natset

(* fun decr ns = decrn 1 ns *)
val decr : natset -> natset

(* fun member n ns = List.exists (fn x => x=n) ns *)
val member : int -> natset -> bool

(* fun toList ns =
	let fun insert (n, ns) = if member n ns then ns else n::ns
	in foldl insert [] ns end *)
val toList : natset -> int list

(* fun union (ns1, ns2) = ns1 @ ns2 *)
val union : natset * natset -> natset

(* fun occurFromTo a b = if a <= b then singleton a @ occurFromTo (a+1) b else [] *)
val occurFromTo : int -> int -> natset

(* splitn n I = (I1, I2) where I1 = intersect(I,{1,..,n}) and I2 = decrn n (I - I1) *)
(* fun splitn n ns = map2 (map (fn x => x-n)) (List.partition (fn x => x<=n) ns) *)
val splitn : int -> natset -> natset * natset

end
