signature RND =
sig

type rndState

val rndNew : int -> rndState
val rndReal : rndState -> real

end
