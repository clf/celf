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

(* Timers collecting statistics about Twelf *)
(* Author: Frank Pfenning *)

signature TIMERS =
sig

  structure Timing : TIMING

  (* Programming interface *)
  val parsing     : Timing.center		(* lexing and parsing *)
  val recon       : Timing.center		(* term reconstruction *)
  val modes       : Timing.center		(* mode checking *)
  val fairness    : Timing.center	        (* construction subordination relation *)
  val solving     : Timing.center		(* solving queries *)
  val unification : Timing.center		(* unification algorithm *)

  (* Warning: time for printing of the answer substitution to a
     query is counted twice here.
  *)
  val total : Timing.sum		(* total time *)

  (* time center f x = y
     if f x = y and time of computing f x is added to center.
     If f x raises an exception, it is re-raised.
  *)
  val time : Timing.center -> ('a -> 'b) -> ('a -> 'b)

  (* External interface *)
  val reset : unit -> unit		(* reset above centers *)
  val check : unit -> unit		(* check timer values *)
  val show : unit -> unit		(* check, then reset *)

end;  (* signature TIMERS *)
