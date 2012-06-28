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

functor Timers (structure Timing' : TIMING)
   : TIMERS =
struct

  structure Timing = Timing'

  val parsing     = Timing.newCenter ("Parsing       ")
  val recon       = Timing.newCenter ("Reconstruction")
  val modes       = Timing.newCenter ("Modes         ")
  val fairness    = Timing.newCenter ("Fairness      ")
  val solving     = Timing.newCenter ("Solving       ")
  val unification = Timing.newCenter ("Unification   ")

  val centers = [parsing, recon, modes, fairness, solving, unification]

  val total    = Timing.sumCenter ("Total         ", centers)

  val time = Timing.time

  fun reset () = List.app Timing.reset centers

  fun check () =
      (List.app (print o Timing.toString) centers;
       print (Timing.sumToString total);
       print "Remember that the success continuation counts into Solving!\n")

  fun show () = (check (); reset ()) 

end;  (* functor Timers *)

structure Timers =
  Timers (structure Timing' = Timing);
