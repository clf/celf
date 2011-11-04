(* Mode checking *)

structure DestCheck:> DESTCHECK =
struct

fun destCheckDecl tyA = ignore (Skel.patterns tyA)

end
