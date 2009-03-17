(* Susp -- support for lazy evaluation *)

structure Susp :> Susp =
struct

datatype 'a thunk = VAL of 'a | THUNK of unit -> 'a;

type 'a susp = 'a thunk ref;

fun delay (f : unit -> 'a) = ref (THUNK f);

fun force (su : 'a susp) : 'a = 
  case !su of
    VAL v   => v 
  | THUNK f => let val v = f () in su := VAL v; v end

(*
Alternative:

type 'a susp = (unit -> 'a) ref

fun delay (f : unit -> 'a) =
	let val s = ref (fn () => raise Fail "Susp dummy")
		val () = s := (fn () =>
				let val v = f ()
					val () = s := (fn () => v)
				in v end)
	in s end

force (s : 'a susp) = !s ()

*)

end
