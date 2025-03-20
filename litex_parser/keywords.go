package litexparser

// var BuiltinSyms = map[string]string{
// 	":":     ":",
// 	"[":     "[",
// 	"]":     "]",
// 	"(":     "(",
// 	")":     ")",
// 	",":     ",",
// 	"$":     "$",
// 	"=":     "=",
// 	"/":     "/",
// 	"+":     "+",
// 	"-":     "-",
// 	"*":     "*",
// 	"^":     "^",
// 	"<":     "<",
// 	">":     ">",
// 	"!":     "!",
// 	"|":     "|",
// 	"~":     "~",
// 	"&":     "&",
// 	".":     ".",
// 	"::":    "::",
// 	"++":    "++",
// 	"--":    "--",
// 	"&&":    "&&",
// 	"||":    "||",
// 	"==":    "==",
// 	"!=":    "!=",
// 	"\\":    "\\",
// 	"?":     "?",
// 	"**":    "**",
// 	"\"":    "\"",
// 	"'":     "'",
// 	"`":     "`",
// 	"=>":    "=>",
// 	";":     ";",
// 	"{":     "{",
// 	"}":     "}",
// 	"\\[":   "\\[",
// 	"\\]":   "\\]",
// 	"#":     "#",
// 	"\\in":  "\\in",
// 	"\\has": "\\has",
// 	"@":     "@", // v@n represents v[n]
// }

// var sortedSymbols []string = sortKeywordSymbols()

// // 初始化排序后的符号列表
// func sortKeywordSymbols() *[]string {
// 	symbols := make([]string, 0, len(BuiltinSyms))
// 	for k := range BuiltinSyms {
// 		symbols = append(symbols, k)
// 	}
// 	sort.Slice(symbols, func(i, j int) bool {
// 		return len(symbols[i]) > len(symbols[j])
// 	})
// 	return &symbols
// }

// // 缓存排序后的符号列表

// // 如果输入字符串从起始位置开始是符号，则返回该符号
// func getKeywordSymbol(inputString string, start int) string {
// 	for _, k := range sortedSymbols {
// 		end := start + len(k)
// 		if end <= len(inputString) {
// 			match := true
// 			for i := 0; i < len(k); i++ {
// 				if inputString[start+i] != k[i] {
// 					match = false
// 					break
// 				}
// 			}
// 			if match {
// 				return k
// 			}
// 		}
// 	}
// 	return ""
// }

const (
	KeywordSetStruct            = "set_struct"
	KeywordType                 = "type"
	KeywordTypeMember           = "type_member"
	KeywordInstanceMember       = "instance_member"
	KeywordForall               = "forall"
	KeywordCond                 = "cond"
	KeywordThen                 = "then"
	KeywordVar                  = "var"
	KeywordFn                   = "fn"
	KeywordProp                 = "prop"
	KeywordKnow                 = "know"
	KeywordExist                = "exist"
	KeywordHave                 = "have"
	KeywordClaim                = "claim"
	KeywordProve                = "prove"
	KeywordPub                  = "pub"
	KeywordImport               = "import"
	KeywordPackage              = "package"
	KeywordNot                  = "not"
	KeywordIs                   = "is"
	KeywordImpl                 = "impl"
	KeywordAny                  = "any"
	KeywordAs                   = "as"
	KeywordAxiom                = "axiom"
	KeywordProveByContradiction = "prove_by_contradiction"
	KeywordThm                  = "thm"
	KeywordWhen                 = "when"
	KeywordRet                  = "ret"

	// Syntax and Semantics Sugar
	KeywordCommutative = "commutative"
	KeywordAssociative = "associative"

	// Builtin Types
	KeywordNat   = "Nat"   // e.g. 0
	KeywordInt   = "Int"   // e.g. -1
	KeywordFloat = "Float" // e.g. -1.1
	KeywordSet   = "Set"   // e.g. to_set(AnyType)

	// Builtin Functions
	KeywordMakeSet = "make_set" // e.g. make_set[TypeName]
	KeywordIn      = "in"
)

// 当引入新的符号的时候，要特别注意getBuiltinSymbol这个函数要重新写
const (
	// Builtin Symbols
	KeywordColon                  = ":"
	KeywordLeftBracket            = "["
	KeywordRightBracket           = "]"
	KeywordLeftParen              = "("
	KeywordRightParen             = ")"
	KeywordComma                  = ","
	KeywordDollar                 = "$"
	KeywordEqual                  = "="
	KeywordSlash                  = "/"
	KeywordPlus                   = "+"
	KeywordMinus                  = "-"
	KeywordStar                   = "*"
	KeywordCaret                  = "^"
	KeywordLess                   = "<"
	KeywordGreater                = ">"
	KeywordExclaim                = "!"
	KeywordPipe                   = "|"
	KeywordTilde                  = "~"
	KeywordAnd                    = "&"
	KeywordDot                    = "."
	KeywordColonColon             = "::"
	KeywordPlusPlus               = "++"
	KeywordMinusMinus             = "--"
	KeywordAndAnd                 = "&&"
	KeywordPipePipe               = "||"
	KeywordEqualEqual             = "=="
	KeywordNotEqual               = "!="
	KeywordBackslash              = "\\"
	KeywordQuestion               = "?"
	KeywordStarStar               = "**"
	KeywordDoubleQuote            = "\""
	KeywordSingleQuote            = "'"
	KeywordBacktick               = "`"
	KeywordEqualGreaterRightArrow = "=>"
	KeywordMinusGreaterRightArrow = "->"
	KeywordSemicolon              = ";"
	KeywordLeftCurly              = "{"
	KeywordRightCurly             = "}"
	KeywordHash                   = "#"
	KeywordAt                     = "@"
)

const (
	// Customizable Operators
	Keyword__Div__          = "__div__"
	Keyword__Add__          = "__add__"
	Keyword__Sub__          = "__sub__"
	Keyword__Mul__          = "__mul__"
	Keyword__Xor__          = "__xor__"
	Keyword__LT__           = "__lt__"
	Keyword__GT__           = "__gt__"
	Keyword__Exclamation__  = "__exclamation__"
	Keyword__Or__           = "__or__"
	Keyword__And__          = "__and__"
	Keyword__AddAdd__       = "__add_add__"
	Keyword__SubSub__       = "__sub_sub__"
	Keyword__AndAnd__       = "__and_and__"
	Keyword__PipePipe__     = "__pipe_pipe__"
	Keyword__EqEq__         = "__eq_eq__"
	Keyword__NE__           = "__ne__"
	Keyword__Pow__          = "__pow__"
	Keyword__LT_EQ__        = "__lt_eq__"
	Keyword__GT_EQ__        = "__gt_eq__"
	Keyword__Union__        = "__union__"
	Keyword__Intersection__ = "__intersection__"
	Keyword__SubsetEq__     = "__subset_eq__"
	Keyword__SupsetEq__     = "__supset_eq__"
	Keyword__Subset__       = "__subset__"
	Keyword__Supset__       = "__supset__"
	Keyword__SubGT__        = "__sub_gt__"
	Keyword__EqGT__         = "__eq_gt__"
)

func getBuiltinSymbol(inputString string, start int) string {
	if start < 0 || start >= len(inputString) {
		return ""
	}

	// Define all possible keywords in order of decreasing length
	// TODO 定义一个函数，手动sort，而不是像这样硬编码地sort
	keywords := []string{
		KeywordEqualGreaterRightArrow, // "=>"
		KeywordMinusGreaterRightArrow, // "->"
		KeywordColonColon,             // "::"
		KeywordPlusPlus,               // "++"
		KeywordMinusMinus,             // "--"
		KeywordAndAnd,                 // "&&"
		KeywordPipePipe,               // "||"
		KeywordEqualEqual,             // "=="
		KeywordNotEqual,               // "!="
		KeywordStarStar,               // "**"
		KeywordColon,                  // ":"
		KeywordLeftBracket,            // "["
		KeywordRightBracket,           // "]"
		KeywordLeftParen,              // "("
		KeywordRightParen,             // ")"
		KeywordComma,                  // ","
		KeywordDollar,                 // "$"
		KeywordEqual,                  // "="
		KeywordSlash,                  // "/"
		KeywordPlus,                   // "+"
		KeywordMinus,                  // "-"
		KeywordStar,                   // "*"
		KeywordCaret,                  // "^"
		KeywordLess,                   // "<"
		KeywordGreater,                // ">"
		KeywordExclaim,                // "!"
		KeywordPipe,                   // "|"
		KeywordTilde,                  // "~"
		KeywordAnd,                    // "&"
		KeywordDot,                    // "."
		KeywordBackslash,              // "\\"
		KeywordQuestion,               // "?"
		KeywordDoubleQuote,            // "\""
		KeywordSingleQuote,            // "'"
		KeywordBacktick,               // "`"
		KeywordSemicolon,              // ";"
		KeywordLeftCurly,              // "{"
		KeywordRightCurly,             // "}"
		KeywordHash,                   // "#"
		KeywordAt,                     // "@"
	}

	// Iterate through keywords and try to match the longest possible
	for _, keyword := range keywords {
		end := start + len(keyword)
		if end <= len(inputString) && inputString[start:end] == keyword {
			return keyword
		}
	}

	// No match found
	return ""
}

func isBuiltinRelationalOperator(op string) bool {
	return op == "<" || op == ">" || op == "<=" || op == ">=" || op == "=" || op == "==" || op == "!="
}
