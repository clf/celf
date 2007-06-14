signature TYP = sig
type t
type 'a F
val inj : t F -> t
val prj : t -> t F
val Fmap : ('a -> 'b) -> 'a F -> 'b F
(* Fmap (fn x => x) == (fn x => x)
   Fmap (f o g) == (Fmap f) o (Fmap g) *)
end

signature REC = sig
structure T : TYP
val fold : ('a T.F -> 'a) -> T.t -> 'a
val unfold : ('a -> 'a T.F) -> 'a -> T.t
val postorderMap : (T.t T.F -> T.t T.F) -> T.t -> T.t
val preorderMap : (T.t T.F -> T.t T.F) -> T.t -> T.t
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

