(*  Celf
 *  Copyright (C) 2008 Anders Schack-Nielsen and Carsten Schürmann
 *
 *  This file is part of Celf.
 *
 *  Celf is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  Celf is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with Celf.  If not, see <http://www.gnu.org/licenses/>.
 *)

structure Main =
struct

structure ClfLrVals =
		ClfLrValsFun(structure Token = LrParser.Token)
structure ClfLex =
		ClfLexFun(structure Tokens = ClfLrVals.Tokens)
structure ClfParser =
		Join(structure ParserData = ClfLrVals.ParserData
				structure Lex = ClfLex
				structure LrParser = LrParser)

fun parseArgs args = case args of
	  [] => raise Fail "No filename given\n"
	| "-s"::seed::args =>
		( print ("Setting random seed "^seed^"\n")
		; PermuteList.setSeed (valOf (Int.fromString seed))
		; parseArgs args )
	| "-d"::args =>
		( print "Enabling double checking\n"
		; TypeCheck.enable ()
		; parseArgs args )
	| "-dfc"::args =>
		( print "Enabling stepwise debugging during forward chaining\n"
		; OpSem.debugForwardChaining := true
		; parseArgs args )
	| "-pi"::args =>
		( print "printImpl := true\n"
		; PrettyPrint.printImpl := true
		; parseArgs args )
	| "-pc1"::args =>
		( print "printLVarCtx := 1\n"
		; PrettyPrint.printLVarCtx := 1
		; parseArgs args )
	| "-pc2"::args =>
		( print "printLVarCtx := 2\n"
		; PrettyPrint.printLVarCtx := 2
		; parseArgs args )
	| "-tu"::args =>
		( print "outputUnify := true\n"
		; Unify.outputUnify := true
		; parseArgs args )
	| "-ta"::args =>
		( print "traceApx := true\n"
		; ApproxTypes.traceApx := true
		; parseArgs args )
	| "-tc"::args =>
		( print "traceApx := true\n"
		; ApproxTypes.traceApx := true
		; parseArgs args )
	| "-te"::args =>
		( print "traceEta := true\n"
		; Eta.traceEta := true
		; parseArgs args )
	| "-tt"::args =>
		( print "traceExact := true\n"
		; ExactTypes.traceExact := true
		; parseArgs args )
	| "-tp1"::args =>
		( print "traceSolve := 1\n"
		; OpSem.traceSolve := 1
		; parseArgs args )
	| "-tp2"::args =>
		( print "traceSolve := 2\n"
		; OpSem.traceSolve := 2
		; parseArgs args )
	| "-tp3"::args =>
		( print "traceSolve := 3\n"
		; OpSem.traceSolve := 3
		; parseArgs args )
	| "-ac"::args =>
		( print "allowConstr := true\n"
		; OpSem.allowConstr := true
		; parseArgs args )
	| "-h"::_ =>
		( print ("Commandline: celf <options> <filename>\n"
				^"Available options:\n"
				^" -s seed : set random seed\n"
				^" -h      : show this\n"
				^" -d      : enable double checking\n"
				^" -dfc    : debug contexts in monadic forward chaining\n"
				^" -ac     : allow leftover constraints in proof search\n"
				^" -pi     : print implicit arguments\n"
				^" -pcL    : print logicvar contexts (L = 1 or 2)\n"
				^" -ta     : trace approximate type reconstruction\n"
				^" -te     : trace eta expansion\n"
				^" -tt     : trace exact type reconstruction\n"
				^" -tu     : trace unifications\n"
				^" -tpL    : trace proof search (L = 1, 2 or 3)\n"
				^" -hquery : show help on queries\n")
		; "" )
	| "-hquery"::_ =>
		( print ("Query format:\n"
				^"#query d e l a ty.\n"
				^" d  : bound on number of let-bindings before aborting\n"
				^"      forward-chaining, * means no bound\n"
				^" e  : expected number of solutions, * means don't know\n"
				^" l  : number of solutions to look for, * means infinite\n"
				^" a  : number of times to execute the query\n"
				^" ty : type to search for proof of\n")
		; "" )
	| f::_ => f

(* Regular invocation of Celf; called from celfMain and celfRegression *)
fun celfMain' args =
	let val () = print "Celf ver 2.8. Copyright (C) 2011\n"
		val filename = parseArgs args
	in if filename = "" then OS.Process.success (* -h was given *) else
	let val () = print ("Reading "^filename^":\n\n")
		val instream = TextIO.openIn filename
		val lexer = ClfParser.makeLexer (fn n => TextIO.inputN (instream,n))
		fun print_parse_error (s,(l1,c1),(l2,c2)) =
			print ("Parse error at "^
				Int.toString l1^","^Int.toString c1^"--"^
				Int.toString l2^","^Int.toString c2^": "^s^"\n")
		val (result : (int * Syntax.decl) list,_) = ClfParser.parse(0,lexer,print_parse_error,())
		val () = TypeRecon.reconstructSignature result
	in OS.Process.success end end

(* Regression testing infrastructure; invoked from celfMain if the first
 * command-line argument to celf is "regression". *)
fun celfRegression args = 
let
   datatype result = 
      Success 
    | Err of Syntax.declError
    | QueryFailed 
    | ParseErr 
    | DoubleCheck of result

   fun parse arg = 
      case arg of
         "success" => Success
       | "undeclId" => Err Syntax.UndeclId
       | "typeErr" => Err Syntax.TypeErr
       | "kindErr" => Err Syntax.KindErr
       | "ambigType" => Err Syntax.AmbigType
       | "modeErr" => Err Syntax.ModeErr
       | "generalErr" => Err Syntax.GeneralErr
       | "queryFailed" => QueryFailed
       | "parseErr" => ParseErr
       | arg => raise Fail ("Unknown outcome: " ^ arg)

   fun str outcome = 
      case outcome of
         Success => "success" 
       | Err Syntax.UndeclId => "undeclId"
       | Err Syntax.TypeErr => "typeErr"
       | Err Syntax.KindErr => "kindErr"
       | Err Syntax.AmbigType => "ambigType"
       | Err Syntax.ModeErr => "modeErr"
       | Err Syntax.GeneralErr => "generalErr"
       | QueryFailed => "queryFailed"
       | ParseErr => "parseErr"
       | DoubleCheck outcome => "DOUBLE-CHECK FAILURE: " ^ str outcome

   fun printErr s = TextIO.output (TextIO.stdErr, s)

   fun getOutcome args = 
    ( Syntax.Signatur.resetSig ()
    ; TypeRecon.resetSignature ()
    ; celfMain' args
    ; Success)
   handle TypeRecon.ReconError ((e, s), _) => Err e
        | TypeRecon.QueryFailed n => QueryFailed
        | ClfParser.ParseError => ParseErr

   fun test (outcome, args) =
   let
      val () = printErr ("celf " ^ String.concatWith " " args 
                         ^ " (expecting `"^str outcome^"')... ") 
      val outcome'' = 
         case getOutcome args of 
            Success => 
             ( printErr "doublecheck... "
             ; case getOutcome ("-d" :: args) of
                  Success => Success
                | out => DoubleCheck out)
          | outcome' => outcome'
   in
      if outcome = outcome''
      then (printErr "yes\n"; NONE)
      else ( printErr ("failed, got `"^str outcome''^"'\n")
           ; SOME (args, "expected `"^str outcome^"`, got `"^str outcome''^"'"))
   end
   handle exn => 
           ( printErr "failed, got unexpected error\n"
           ; SOME (args, "expected `" ^ str outcome ^ "', got unexpected \
                             \failure `" ^ exnMessage exn ^ "'"))
 
   fun testfile file accum = 
   let fun mapper line = 
          case String.fields (fn x => x = #"#") line of 
             [] => [] 
           | x :: _ => String.tokens Char.isSpace x
   in case Option.map mapper (TextIO.inputLine file) of
         NONE => (TextIO.closeIn file; accum)
       | SOME [] => testfile file accum
       | SOME (arg :: args) => testfile file (test (parse arg, args) :: accum)
   end

   fun testfiles [] accum = rev accum
     | testfiles (file :: files) accum =
       let 
          val oldDir = OS.FileSys.getDir ()
          val {dir, ...} = OS.Path.splitDirFile file
          val file = TextIO.openIn file
       in
        ( if dir = "" then () else OS.FileSys.chDir dir
        ; testfiles files (testfile file accum)
        before OS.FileSys.chDir oldDir)
       end

   val () = T.beQuiet := true
   val results = rev (testfiles args [])
   val successes = List.foldr (fn (NONE, n) => n+1 | (_, n) => n) 0 results
   val failures = List.foldr (fn (SOME _, n) => n+1 | (_, n) => n) 0 results
in
 ( T.beQuiet := false
 ; print ("Result: " ^ Int.toString (length results) ^ " tests\n")
 ; print ("Successful tests: " ^ Int.toString successes ^ "\n")
 ; print ("Failed tests: " ^ Int.toString failures ^ "\n\n")
 ; if failures > 0 then print ("Details:\n\n") else ()
 ; app (fn NONE => ()
         | SOME (args, msg) => 
            ( print ("celf " ^ String.concatWith " " args ^ "\n")
            ; print (" - " ^ msg ^ "\n\n")))
      results
 ; if failures = 0 then OS.Process.success else OS.Process.failure)
end handle exn => 
            ( T.beQuiet := false
            ; print ("\nREGRESSION ERROR: " ^ exnMessage exn ^ "\n\n")
            ; OS.Process.failure)


fun celfMain (_, args) = 
   if not (null args) andalso hd args = "regression" 
   then celfRegression (tl args)
   else celfMain' args 
handle TypeRecon.ReconError (es, ldec) =>
       let
          fun declToStr (linenum, dec) =
          let 
             val decstr = 
                case dec of
                   Syntax.ConstDecl (id, _, _) => "declaration of " ^ id
                 | Syntax.TypeAbbrev (id, _) => "declaration of " ^ id
                 | Syntax.ObjAbbrev (id, _, _) => "declaration of " ^ id
                 | Syntax.Query _ => "query"
                 | Syntax.Trace _ => "trace"
                 | Syntax.Exec _ => "exec"
                 | Syntax.Mode (id,_,_) => "mode declaration of " ^ id
          in
             decstr ^ " on line " ^ Int.toString linenum
          end

          val decstr = declToStr ldec

          val d = 
             case es of
                (Syntax.UndeclId, c) => 
                   "Undeclared identifier \"" ^ c ^ "\" in " ^ decstr
              | (Syntax.TypeErr, s) => 
                   "Type-checking failed in " ^ decstr ^ ":\n" ^ s 
              | (Syntax.KindErr, s) => 
                   "Kind-checking failed in " ^ decstr ^ ":\n" ^ s 
              | (Syntax.AmbigType, "") => 
                   "Ambiguous typing in " ^ decstr
              | (Syntax.AmbigType, s) => 
                   "Ambiguous typing in " ^ decstr ^ ":\n" ^ s
              | (Syntax.ModeErr, s) =>
                   "Mode checking failed in " ^ decstr ^ ":\n"^s
              | (Syntax.GeneralErr, s) => 
                   "Error in " ^ decstr ^ ":\n" ^ s 
       in 
        ( print ("\n" ^ d ^ "\n\n")
        ; OS.Process.failure)
       end
     | TypeRecon.QueryFailed n =>
        ( print ("\nQuery failed on line " ^ Int.toString n ^ "\n\n")
        ; OS.Process.failure)
     | exn => 
        ( print ("Unhandled exception " ^ exnName exn ^ ":\n")
        ; print (exnMessage exn^"\n")
       ; OS.Process.failure)
end
