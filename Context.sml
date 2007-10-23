structure Context :> CONTEXT =
struct

exception ExnCtx of string

datatype mode = UN | LIN | NO
type 'a context = (string * 'a * mode) list

fun ctx2list ctx = ctx
fun ctxCons e ctx = e::ctx

fun ctxMap f ctx = map (fn (x, A, t) => (x, f A, t)) ctx

val emptyCtx = []

(* ctxDelLin : context -> context *)
fun ctxDelLin ctx =
	let fun delLin' (entry as (_, _, UN)) = entry
		  | delLin' (entry as (_, _, NO)) = entry
		  | delLin' (x, A, LIN) = (x, A, NO)
	in map delLin' ctx end

fun use _ UN = UN
  | use _ LIN = NO
  | use y NO = raise Fail ("Linear variable "^y^" can't be used twice/here\n")

(* ctxLookupNum : 'a context * int -> 'a context * 'a *)
fun ctxLookupNum (ctx, n) =
	let fun ctxLookup' (i, ctxfront, []) = raise Fail "Internal error: End of context\n"
		  | ctxLookup' (1, ctxfront, (x, A, f)::ctx) =
				(List.revAppend (ctxfront, (x, A, use x f)::ctx), A)
		  | ctxLookup' (i, ctxfront, c::ctx) = ctxLookup' (i-1, c::ctxfront, ctx)
	in ctxLookup' (n, [], ctx) end

(* ctxLookupName : 'a context * string -> (int * 'a * 'a context) option *)
fun ctxLookupName (ctx, y) =
	let fun ctxLookup' (i, ctx, []) = NONE
		  | ctxLookup' (i, ctxfront, (x, A, f)::ctx) =
				if x=y then SOME (i, A, List.revAppend (ctxfront, (x, A, use x f)::ctx))
				else ctxLookup' (i+1, (x, A, f)::ctxfront, ctx)
	in ctxLookup' (1, [], ctx) end

(* ctxPushUN : string * 'a * 'a context -> 'a context *)
fun ctxPushUN (x, A, ctx) = (x, A, UN) :: ctx

(* ctxPushLIN : string * 'a * 'a context -> 'a context *)
fun ctxPushLIN (x, A, ctx) = (x, A, LIN) :: ctx

(* ctxPopUN : 'a context -> 'a context *)
fun ctxPopUN ((_, _, UN)::ctx) = ctx
  | ctxPopUN _ = raise Fail "Internal error: ctxPopUN"

(* ctxPopLIN : bool * 'a context -> 'a context *)
fun ctxPopLIN (_, (_, _, NO)::ctx) = ctx
  | ctxPopLIN (true, (_, _, LIN)::ctx) = ctx
  | ctxPopLIN (false, (x, _, LIN)::ctx) = raise ExnCtx (x^" doesn't occur\n")
  | ctxPopLIN _ = raise Fail "Internal error: ctxPopLIN"

(* ctxPopLINopt : bool * 'a context -> 'a context option *)
fun ctxPopLINopt tCtx = SOME (ctxPopLIN tCtx) handle ExnCtx _ => NONE

fun addJoin (t1, t2) ((x, A, f1), (_, _, f2)) =
	let val f = case (t1, f1, t2, f2) of
					(_, UN, _, UN) => UN
				  | (_, NO, _, NO) => NO
				  | (_, LIN, _, LIN) => LIN
				  | (_, NO, true, LIN) => NO
				  | (_, NO, false, LIN) => raise ExnCtx "Contexts can't join\n"
				  | (true, LIN, _, NO) => NO
				  | (false, LIN, _, NO) => raise ExnCtx "Contexts can't join\n"
				  | _ => raise Fail "Internal error: context misalignment\n"
	in (x, A, f) end

(* ctxAddJoin : bool * bool -> 'a context * 'a context -> 'a context *)
fun ctxAddJoin topFlags ctxs = ListPair.mapEq (addJoin topFlags) ctxs

(* ctxAddJoinOpt : bool * bool -> 'a context * 'a context -> 'a context option *)
fun ctxAddJoinOpt topFlags ctxs = SOME (ctxAddJoin topFlags ctxs) handle ExnCtx _ => NONE

end
