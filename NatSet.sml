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

type natset = int list (* sorted in increasing order with no duplicates *)

val empty = []

fun isEmpty (ns : natset) = ns = []

fun singleton n = if n >= 1 then [n] else raise ExnNatSet

(*fun decrn n ns = List.filter (fn x => x>=1) (map (fn x => x-n) ns)*)
fun decrn n [] = []
  | decrn n (n1::ns) = if n >= n1 then decrn n ns else map (fn x => x-n) (n1::ns)

fun decr ns = decrn 1 ns

(*fun member n (ns : natset) = List.exists (fn x => x=n) ns*)
fun member _ [] = false
  | member n (n1::ns) = n = n1 orelse (n > n1 andalso member n ns)

fun toList ns = ns

fun union ([], ns2) = ns2
  | union (ns1, []) = ns1
  | union (n1::ns1, n2::ns2) =
	if n1 = n2 then n1 :: union (ns1, ns2)
	else if n1 < n2 then n1 :: union (ns1, n2::ns2)
	else (* n2 < n1 *) n2 :: union (n1::ns1, ns2)

fun occurFromTo' (a, b, acc) = if a <= b then occurFromTo' (a, b-1, b::acc) else acc
fun occurFromTo a b = if a >= 1 then occurFromTo' (a, b, []) else raise ExnNatSet

(* splitn n I = (I1, I2) where I1 = intersect(I,{1,..,n}) and I2 = decrn n (I - I1) *)
fun splitn n ns = map2 (map (fn x => x-n)) (List.partition (fn x => x<=n) ns)

end
