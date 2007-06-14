structure ClfLrVals =
		ClfLrValsFun(structure Token = LrParser.Token)
structure ClfLex =
		ClfLexFun(structure Tokens = ClfLrVals.Tokens)
structure ClfParser =
		Join(structure ParserData = ClfLrVals.ParserData
				structure Lex = ClfLex
				structure LrParser = LrParser)

val filename =
	case CommandLine.arguments () of
		  [] => raise Fail "No filename given\n"
		| f::_ => (print ("Reading "^f^":\n\n"); f)

val instream = TextIO.openIn filename

val lexer = ClfParser.makeLexer (fn n => TextIO.inputN (instream,n))
fun print_parse_error (s,(l1,c1),(l2,c2)) =
	print ("Parse error at "^
		Int.toString l1^","^Int.toString c1^"--"^
		Int.toString l2^","^Int.toString c2^": "^s^"\n")
val (result : Syntax.decl list,_) = ClfParser.parse(0,lexer,print_parse_error,())

val () = TypeRecon.reconstructSignature result


