signature GOALPATTERN =
sig

  type goalPattern = (string * string option) option

  (* goalPattern computes the "shape" of the first subgoal of a clause
   * This subgoal must be a  f1 (f2 ..., ...) where f1 is an empty family
   * and f2 is a constructor *)
  val goalPattern : Syntax.nfAsyncType -> goalPattern

end

