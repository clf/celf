structure SimpleDB = struct

open Syntax
structure T = ClfTerms

fun transA (typA: AsyncType.t) = 
  case AsyncType.prj typA of 
    TLPi (_, typS, typA) => T.Lolli' (transS typS, transA typA)
  | AddProd (typA1, typA2) => T.With' (transA typA1, transA typA2)
  | TMonad typS => T.Monad' (transS typS)
  | TAtomic (a, _) => T.Atom' (Symbol.symbol a)
  | TAbbrev (_, typA) => transA typA

and transS (typS: SyncType.t) = 
  case SyncType.prj typS of 
    LExists (_, typS1, typS2) => T.Tensor' (transS typS1, transS typS2)
  | TOne => T.One'
  | TDown typA => T.Down' (T.Lin', transA typA)
  | TAffi typA => T.Down' (T.Aff', transA typA)
  | TBang typA => T.Down' (T.Per', transA typA)

fun printSubord s (h1, h2) = 
   print (s ^ T.strHead h1 ^ " <| " ^ T.strHead h2 ^ "\n")

fun add dec = 
  let val print = print in
    case dec of
      ConstDecl (a, num_implicit_pis, Ki _) => 
        let 
          val x = Symbol.symbol a

          (* Add basic fact to database *)
          val () = ClfTables.assertTyp x  
        in
          print ("==SimpleDB: Type Declaration " ^ a ^ "==\n") 
        end
    | ConstDecl (c, num_implicit_pis, Ty typA) => 
        let 
          val x = Symbol.symbol c
          val ty = transA typA

          (* Add signature fact to database *)
          val () = ClfTables.assertCon (x, ty)

          (* Calculate new subordination information *)
          val _ = ClfSearch.saturateWSubordA ty T.MapWorld.empty
	  val subords = ClfTables.subordA_1_lookup (!ClfTables.subordA_1, ty)

          (* Add new subordination information to database *)
          val () = app ClfTables.assertSubord subords
          val _ = ClfSearch.saturateWSubord T.MapWorld.empty
        in 
          print ("==SimpleDB: Constant Declaration ")
          ; print (c ^ ": " ^ T.strNeg ty ^ "==\n")
          ; print ("    Discovered subordination facts: \n")
          ; app (printSubord "    ") subords 
        end
    | TypeAbbrev _ => () (* Nothing to do *)
    | ObjAbbrev _ => () (* Nothing to do *)
    | Query _ => () (* Nothing to do *)
    | Mode _ => () (* Nothing to do *)
  end

fun conclude () = 
  let
    val _ = ClfSearch.saturateWPosAtom T.MapWorld.empty
  in
    print ("==SimpleDB: Concluding==\n")
    ; print ("  Subordination relation:\n")
    ; app (printSubord "    ") (!ClfTables.subord_3)
    ; print ("  Atoms that can behave as positive (modulo linearity issues):\n")
    ; app (fn x => print ("    " ^ Symbol.name x ^ "\n")) 
        (!ClfTables.posAtom_1)
    ; if null (ClfTables.subord_4_lookup
                (!ClfTables.subord_4, T.Monadic'))
      then print ("Strongly in the semantic effects fragment;\n\
                  \monadic is not subordinate to anything.\n")
      else if null (ClfTables.subord_0_lookup
                     (!ClfTables.subord_0, (T.Monadic', T.Monadic')))
      then print ("Weakly in the semantic effects fragment;\n\
                  \monadic is not subordinate to itself.\n\n")        
      else print ("Not in the semantic effects fragment;\n\
                  \monadic is self-subordinate\n")
  end

end
