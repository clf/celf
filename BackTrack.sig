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
