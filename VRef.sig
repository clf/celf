signature VREF =
sig

type 'a vref

val vref : 'a -> 'a vref

val ::= : 'a vref * 'a -> unit

val !! : 'a vref -> 'a

val eq : 'a vref * 'a vref -> bool

end
