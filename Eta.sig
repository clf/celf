signature ETA =
sig

val etaContract : exn -> Syntax.obj -> int

val etaExpand : Syntax.apxAsyncType * Syntax.head * Syntax.apxAsyncType * Syntax.spine -> Syntax.obj
val etaExpandKind : Syntax.kind -> Syntax.kind
val etaExpandType : Syntax.asyncType -> Syntax.asyncType
val etaExpandTypeSpine : Syntax.typeSpine * Syntax.apxKind -> Syntax.typeSpine
val etaExpandSyncType : Syntax.syncType -> Syntax.syncType
val etaExpandObj : Syntax.obj * Syntax.apxAsyncType -> Syntax.obj
val etaExpandHead : Syntax.head -> Syntax.head
val etaExpandSpine : Syntax.spine * Syntax.apxAsyncType -> Syntax.spine
val etaExpandExp : Syntax.expObj * Syntax.apxSyncType -> Syntax.expObj
val etaExpandPattern : Syntax.pattern -> Syntax.pattern
val etaExpandMonadObj : Syntax.monadObj * Syntax.apxSyncType -> Syntax.monadObj

end
