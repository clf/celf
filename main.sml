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
	| "-h"::_ =>
		( print ("Commandline: celf <options> <filename>\n"
				^"Available options:\n"
				^" -s seed : set random seed\n"
				^" -h      : show this\n"
				^" -d      : enable double checking\n"
				^" -pi     : print implicit arguments\n"
				^" -ta     : trace approximate type reconstruction\n"
				^" -te     : trace eta expansion\n"
				^" -tt     : trace exact type reconstruction\n"
				^" -tu     : trace unifications\n")
		; "" )
	| f::_ => f

fun celfMain' args =
	let val () = print "Celf ver 1.0. Copyright (C) 2008\n"
		val filename = parseArgs args
	in if filename = "" then OS.Process.success (* -h was given *) else
	let val () = print ("Reading "^filename^":\n\n")
		val instream = TextIO.openIn filename
		val lexer = ClfParser.makeLexer (fn n => TextIO.inputN (instream,n))
		fun print_parse_error (s,(l1,c1),(l2,c2)) =
			print ("Parse error at "^
				Int.toString l1^","^Int.toString c1^"--"^
				Int.toString l2^","^Int.toString c2^": "^s^"\n")
		val (result : Syntax.decl list,_) = ClfParser.parse(0,lexer,print_parse_error,())
		val () = TypeRecon.reconstructSignature result
	in OS.Process.success end end

fun celfMain (_, args) = celfMain' args handle e =>
	( print ("Unhandled exception:\n"^exnMessage e^"\n")
	; OS.Process.failure )

end
