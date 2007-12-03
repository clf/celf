signature WHNF =
sig

structure Syn : SYNTAX_CORE2
val whnfObj : Syn.obj -> (Syn.spine, Syn.expObj, Syn.obj) Syn.nfObjFF
val whnfExp : Syn.expObj ->
	(Syn.head * Syn.spine, Syn.monadObj, Syn.pattern, Syn.expObj) Syn.expObjFF

val appendSpine : Syn.spine * Syn.spine -> Syn.spine

(*
val whnfLetSpine : Syntax.expObj -> Syntax.expObj

val normalizeKind : Syntax.kind -> Syntax.kind
val normalizeType : Syntax.asyncType -> Syntax.asyncType
val normalizeObj : Syntax.obj -> Syntax.obj
*)

end
