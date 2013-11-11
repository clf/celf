structure Backend :> BACKEND =
struct

open InternalSyntax
open SymbTable

exception QueryFailed of int

(******************** IMPLICITVARSCONVERT **************************)
fun depInc NONE n = n
  | depInc (SOME _) n = n+1

fun uc2xKind lookup n ki =
    case ki of
	Type => Type
      | KPi (x, A, K) => KPi (x, uc2xType lookup n A, uc2xKind lookup (depInc x n) K)

and uc2xType lookup n ty =
    case ty of
	TLPi (p, A, B) => TLPi (p, uc2xSyncType lookup n A, uc2xType lookup (n + numBinds p) B)
      | AddProd (A, B) => AddProd (uc2xType lookup n A, uc2xType lookup n B)
      | TMonad S => TMonad (uc2xSyncType lookup n S)
      | TAtomic (a, S) => TAtomic (a, uc2xTypeSpine lookup n S)

and uc2xTypeSpine lookup n sp =
    case sp of
        TNil => TNil
      | TApp (ob, sp') => TApp (uc2xObj lookup n ob, uc2xTypeSpine lookup n sp')

and uc2xSyncType lookup n sty =
    case sty of
	LExists (p, S1, S2) => LExists (p, uc2xSyncType lookup n S1, uc2xSyncType lookup (n + numBinds p) S2)
      | TOne => TOne
      | TDown A => TDown (uc2xType lookup n A)
      | TAffi A => TAffi (uc2xType lookup n A)
      | TBang A => TBang (uc2xType lookup n A)

and uc2xObj lookup n ob =
    case ob of
	LLam (p, N) => LLam (p, uc2xObj lookup (n + numBinds p) N)
      | AddPair (N1, N2) => AddPair (uc2xObj lookup n N1, uc2xObj lookup n N2)
      | Monad E => Monad (uc2xExp lookup n E)
      | Atomic (H, S) => Atomic (uc2xHead lookup n H, uc2xSpine lookup n S)
      | Clo _ => raise Fail "Internal error: uc2xSpine Clo"


and uc2xHead lookup n h =
    case h of
	Const c => Const c
      | UCVar v => lookup n v
      | LogicVar X =>
	LogicVar (updS (updTy X (uc2xType lookup (foldSubst (fn (_,k) => k+1) (fn k => n-k) (#s X)) (#ty X)))
		       (mapSubst (uc2xObj lookup n) (#s X)))
      | Var vn => Var vn

and uc2xSpine lookup n sp =
    case sp of
        Nil => Nil
      | LApp (m, sp') => LApp (uc2xMonadObj lookup n m, uc2xSpine lookup n sp')
      | ProjLeft sp' => ProjLeft (uc2xSpine lookup n sp')
      | ProjRight sp' => ProjRight (uc2xSpine lookup n sp')
      | SClo _ => raise Fail "Internal error: uc2xSpine SClo"

and uc2xExp lookup n e =
    case e of
	Let (eps, m) => raise Fail "Internal error: TODO uc2xExp"

and uc2xMonadObj lookup n m =
    case m of
        DepPair (m1, m2) => DepPair (uc2xMonadObj lookup n m1, uc2xMonadObj lookup n m2)
      | One => One
      | Down ob => Down (uc2xObj lookup n ob)
      | Affi ob => Affi (uc2xObj lookup n ob)
      | Bang ob => Bang (uc2xObj lookup n ob)
      | MonUndef => MonUndef


fun ctx2Lookup ctx =
	let fun l [] n (x : string) = raise Fail "Internal error: UCVar not in implicits"
		  | l ((y, _)::ys) n x = if x=y then Var (INT, n) else l ys (n+1) x
	in l ctx end

(* convUCVars2LogicVarsType : asyncType -> asyncType * (string * obj) list *)
fun convUCVars2LogicVarsType ty =
    let
      val table = ref (mapTable (fn A => newLVar (AbstractToInternal.typeToInternal A)) (ImplicitVars.getUCTable ()))
      fun uc2lvar n x =
          case InternalSubst.substObj (valOf (peek (!table, x)), Shift n) of
	      Atomic (X as LogicVar _, _) => X
	    | _ => raise Fail "Internal error: uc2lvar"
      val imps = ImplicitVars.sort ()
      fun convX x = table := insert (!table, x, uc2xObj uc2lvar 0 (valOf (peek (!table, x))))
      val () = app (convX o #1) imps
    in
      (uc2xType uc2lvar 0 ty, toList (!table))
    end

(******************** IMPLICITVARSCONVERT **************************)


fun processTrace (count, sty) =
    let
      val () =
          print ("Trace "
                 ^(case count of NONE => "*" | SOME i => Int.toString i)
                 ^" "^PrettyPrinting.printSyncType sty^"\n")
      val (count', _) = OpSemModed.trace count sty
    in
      if not (isSome count) orelse count = SOME count'
      then print ("Success: "^Int.toString count'^" steps\n")
      else ( print ("Trace failed, expected "^Int.toString (valOf count)
                    ^" steps but only "^Int.toString count'
                    ^" taken\n")
           ; raise QueryFailed 37)
    end

fun processExec (count, sty) =
    let
      val () =
          print ("Exec "
                 ^(case count of NONE => "*" | SOME i => Int.toString i)
                 ^" "^PrettyPrinting.printSyncType sty^"\n")
      val (count', context) = OpSemModed.exec count sty
    in
      if not (isSome count) orelse count = SOME count'
      then ( print ("Success: "^Int.toString count'^" steps\n"))
      else ( print ("Exec failed, expected "^Int.toString (valOf count)
                    ^" steps but only "^Int.toString count'
                    ^" taken\n")
           ; raise QueryFailed 37)
    end



fun processDecl dec =
    let
      fun processQuery (d, e, l, a, ty) =
          (* d : let-depth-bound * = inf
           * e : expected number of solutions * = ?
           * l : number of solutions to look for * = inf
           * a : number of times to execute the query
           *)
          let
            fun n2str (SOME n) = Int.toString n
              | n2str NONE = "*"
            val (implty, lvars) = convUCVars2LogicVarsType ty
            fun printInst (x, ob) =
                print (" #"^x^" = "^PrettyPrinting.printObj ob^"\n")
            exception stopSearchExn
            val solCount = ref 0
            fun scMatch N = ( (* print ("Solution: "^PrettyPrint.printObj N^"\n") *)
              (* ;  *)app printInst lvars
                    ; solCount := !solCount + 1
                    ; if l = SOME (!solCount)
                      then raise stopSearchExn
                      else () )
            fun runQuery 0 = false
              | runQuery n =
                ( solCount := 0
                ; if a > 1
                  then print ("Iteration "^Int.toString (a+1-n)^"\n")
                  else ()
                ; Timers.time Timers.solving (fn () => OpSemModed.solveEC (implty, scMatch)) ()
                ; e = SOME (!solCount) orelse runQuery (n-1) )
            val fcLimit = OpSem.fcLimit
            val () = OpSem.fcLimit := d
             (* TODO: check that query is a goal. The code below does not work because the mode
              * checker does not handle UCVar's (ImplicitVars) present in queries. They should be
              * treated as existentials *)
             (* fun isGoal ty = ((ModeCheck.modeCheckGoal (normalizeType ty); true) *)
             (*                  handle ModeCheck.ModeCheckError _ => false) *)
             fun isGoal _ = true

             val () = print "********* MODED QUERY ****************\n"
         in
           if a = 0 orelse l = SOME 0
           then print "Ignoring query\n"
           else if a >= 2 andalso isSome l
           then raise Syntax.ExnDeclError (Syntax.GeneralErr,
                                    "Malformed query (D,E,L,A): A>1 and L<>*\n\
                                    \Should not do simultaneous monad and\
                                    \ backtrack exploration\n")
           else if isSome e andalso isSome l andalso valOf e >= valOf l
           then raise Syntax.ExnDeclError (Syntax.GeneralErr,
                                    "Malformed query (D,E,L,A): E>=L\n\
                                    \Uncheckable since expected number of\
                                    \ solutions is\ngreater than the number of\
                                    \ solutions to look for\n")
           else if (runQuery a handle stopSearchExn => false)
           then print "Query ok.\n"
           else if isSome e
           then
             ( print "Query failed\n"
             ; raise QueryFailed 37) (* TODO: fix this magic number *)
           else ()
         end

      val intDec = AbstractToInternal.declToInternal dec

    in
      Signature.insertDecl intDec
    ; case intDec of
          Query (OpSemMatch, d, e, l, a, ty) => processQuery (d,e,l,a,ty)
        | Trace (count, sty) => processTrace (count, sty)
        | Exec (count, sty) => processTrace (count, sty)
        | _ => ()
    end

end
