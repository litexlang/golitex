package litexparser

import "sort"

const (
	KeywordInterface            = "interface"
	KeywordType                 = "type"
	KeywordTypeMember           = "type_member"
	KeywordInstanceMember       = "instance_member"
	KeywordForall               = "forall"
	KeywordCond                 = "cond"
	KeywordThen                 = "then"
	KeywordObj                  = "obj"
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
	KeywordNat   = "nat"   // e.g. 0
	KeywordInt   = "int"   // e.g. -1
	KeywordFloat = "float" // e.g. -1.1
	KeywordSet   = "set"   // e.g. to_set(AnyType)

	// Builtin Functions
	KeywordIn = "in"
)

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
	//! 每次引入新的Symbol，要往getBuiltinSymbol里加东西
)

var BuiltinSymbolArray = []string{
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

// Customizable Operators

const (
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

	sort.Strings(BuiltinSymbolArray) // 为了安全性，sort一下

	// Iterate through keywords and try to match the longest possible
	for _, keyword := range BuiltinSymbolArray {
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
