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

(* Timing utilities based on SML'97 Standard Library *)
(* Author: Frank Pfenning *)

signature TIMING =
sig

  val init : unit -> unit

  type center
  val newCenter : string -> center
  val reset : center -> unit
  val time : center -> ('a -> 'b) -> ('a -> 'b)

  type sum
  val sumCenter : string * center list -> sum

  val toString : center -> string
  val sumToString : sum -> string

end;  (* signature TIMING *)
