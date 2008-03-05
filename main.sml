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
		( print ("Commandline: celf [-s seed] [-h] [-d] [-pi] <filename>\n"
				^" -s seed : set random seed\n"
				^" -h      : show this\n"
				^" -d      : enable double checking\n"
				^" -pi     : print implicit arguments\n"
				^" -ta     : trace approximate type reconstruction\n"
				^" -te     : trace eta expansion\n"
				^" -tt     : trace exact type reconstruction\n"
				^" -tu     : trace unifications\n")
		; raise Fail "Commandline help" )
	| f::_ => f

val filename = parseArgs (CommandLine.arguments ())

val () = print ("Reading "^filename^":\n\n")

val instream = TextIO.openIn filename

val lexer = ClfParser.makeLexer (fn n => TextIO.inputN (instream,n))
fun print_parse_error (s,(l1,c1),(l2,c2)) =
	print ("Parse error at "^
		Int.toString l1^","^Int.toString c1^"--"^
		Int.toString l2^","^Int.toString c2^": "^s^"\n")
val (result : Syntax.decl list,_) = ClfParser.parse(0,lexer,print_parse_error,())

val () = TypeRecon.reconstructSignature result


