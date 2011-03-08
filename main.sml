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

fun celfMain' args =
	let val () = print "Celf ver 2.7. Copyright (C) 2011\n"
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

fun celfMain (_, args) = celfMain' args handle e =>
	( print ("Unhandled exception:\n"^exnMessage e^"\n")
	; OS.Process.failure )

end
