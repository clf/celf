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

signature TLU_NatSet = TOP_LEVEL_UTIL
structure NatSet :> NATSET =
struct

exception ExnNatSet

type natset = int list
val empty = []
fun isEmpty (ns : natset) = ns = []
fun singleton n = if n >= 1 then [n] else raise ExnNatSet
fun decrn n ns = List.filter (fn x => x>=1) (map (fn x => x-n) ns)
fun decr ns = decrn 1 ns
fun member n (ns : natset) = List.exists (fn x => x=n) ns
fun toList ns =
	let fun insert (n, ns) = if member n ns then ns else n::ns
	in foldl insert [] ns end
fun union (ns1, ns2) = ns1 @ ns2
fun occurFromTo' a b = if a <= b then a::occurFromTo' (a+1) b else []
fun occurFromTo a b = if a >= 1 then occurFromTo' a b else raise ExnNatSet
(* splitn n I = (I1, I2) where I1 = intersect(I,{1,..,n}) and I2 = decrn n (I - I1) *)
fun splitn n ns = map2 (map (fn x => x-n)) (List.partition (fn x => x<=n) ns)

end
