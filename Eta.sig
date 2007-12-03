signature ETA =
sig

type context

val etaContract : exn -> Syntax.obj -> int

val etaExpand : Syntax.apxAsyncType * Syntax.head * Syntax.spine -> Syntax.obj
val etaExpandKind : context * Syntax.kind -> Syntax.kind
val etaExpandType : context * Syntax.asyncType -> Syntax.asyncType
val etaExpandTypeSpine : context * Syntax.typeSpine * Syntax.apxKind -> Syntax.typeSpine
val etaExpandSyncType : context * Syntax.syncType -> Syntax.syncType
val etaExpandObj : context * Syntax.obj * Syntax.apxAsyncType -> Syntax.obj
val etaExpandHead : context * Syntax.head -> Syntax.head * Syntax.apxAsyncType
val etaExpandSpine : context * Syntax.spine * Syntax.apxAsyncType -> Syntax.spine
val etaExpandExp : context * Syntax.expObj * Syntax.apxSyncType -> Syntax.expObj
val etaExpandPattern : context * Syntax.pattern -> Syntax.pattern
val etaExpandMonadObj : context * Syntax.monadObj * Syntax.apxSyncType -> Syntax.monadObj

val etaExpandKindEC : Syntax.kind -> Syntax.kind
val etaExpandTypeEC : Syntax.asyncType -> Syntax.asyncType
val etaExpandObjEC : Syntax.obj * Syntax.apxAsyncType -> Syntax.obj

end
