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

signature BACKTRACK =
sig

(* trails a state update and saves the undo function for future backtracking *)
val trailUpdate : (unit -> unit) -> unit

(* backtrackC f
 * run "f commitExn", then backtrack updates done by f unless
 * commitExn x has been raised in which case we erase the backtracking 
 * marks and return SOME x.
 *)
val backtrackC : (('a -> exn) -> unit) -> 'a option

(* backtrack f
 * run "f", then backtrack updates done by f, i.e.:
 * val backtrack f = let val NONE = backtrackC (fn _ => f ()) in () end *)
val backtrack : (unit -> unit) -> unit

end
