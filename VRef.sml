structure VRef :> VREF =
struct

open BackTrack

type 'a vref = 'a ref

fun vref x = ref x

fun ::= (r, x) =
	( trailUpdate (let val old = !r in fn () => r := old end)
	; r := x )

val !! = !

val eq = op=

end
