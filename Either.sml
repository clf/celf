structure Either =
struct

datatype ('a, 'b) either = LEFT of 'a | RIGHT of 'b

fun leftOf (LEFT l) = l
  | leftOf (RIGHT _) = raise Option

fun rightOf (LEFT _) = raise Option
  | rightOf (RIGHT r) = r

end
