package litexglobal

import "sort"

const ScopeIndent = "    "

const (
	KeywordInterface            = "interface"
	KeywordType                 = "type"
	KeywordSet                  = "set"
	KeywordForall               = "forall"
	KeywordWhen                 = "when"
	KeywordCond                 = "cond" // 必须存在，因为有时候只有要求没then
	KeywordThen                 = "then"
	KeywordObj                  = "obj"
	KeywordFn                   = "fn"
	KeywordProp                 = "prop"
	KeywordKnow                 = "know"
	KeywordExistProp            = "exist_prop"
	KeywordHave                 = "have"
	KeywordClaim                = "claim"
	KeywordProve                = "prove"
	KeywordPub                  = "pub"
	KeywordImport               = "import"
	KeywordPackage              = "package"
	KeywordNot                  = "not"
	KeywordImpl                 = "impl"
	KeywordAs                   = "as"
	KeywordAxiom                = "axiom" // syntax sugar for: prop + know forall
	KeywordProveByContradiction = "prove_by_contradiction"
	KeywordThm                  = "thm"  // syntax sugar for: prop + prove
	KeywordSelf                 = "self" // return value of a function; refer to an instance of the type or set we are defining

	// Syntax and Semantics Sugar
	KeywordCommutative = "commutative"
	KeywordAssociative = "associative"

	// Builtin Types
	KeywordNat      = "nat"      // e.g. 0
	KeywordInt      = "int"      // e.g. -1
	KeywordRational = "rational" // e.g. -1.1
	KeywordReal     = "real"     // e.g. pi

	// Builtin Functions
	KeywordIs = "is"
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

func IsBuiltinSymbol(name string) bool {
	for _, s := range BuiltinSymbolArray {
		if s == name {
			return true
		}
	}
	return false
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

func GetBuiltinSymbol(inputString string, start int) string {
	if start < 0 || start >= len(inputString) {
		return ""
	}

	// 自定义排序规则，确保较长的符号排在前面
	sort.Slice(BuiltinSymbolArray, func(i, j int) bool {
		if len(BuiltinSymbolArray[i]) != len(BuiltinSymbolArray[j]) {
			return len(BuiltinSymbolArray[i]) > len(BuiltinSymbolArray[j])
		}
		return BuiltinSymbolArray[i] < BuiltinSymbolArray[j]
	})

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

func IsBuiltinRelaOpt(op string) bool {
	return op == "<" || op == ">" || op == "<=" || op == ">=" || op == "=" || op == "==" || op == "!="
}

type FcInfixOptPrecedence int

// TODO: implement other operators. How logical operators work is also not implemented
const (
	PrecLowest         FcInfixOptPrecedence = iota
	PrecAssignment                          // =
	PrecOr                                  // or
	PrecAnd                                 // and
	PrecEquality                            // == !=
	PrecComparison                          // < > <= >=
	PrecAddition                            // + -
	PrecMultiplication                      // / *
	PrecUnary                               // - !
	PrecExponentiation                      // ^
)

var PrecedenceMap = map[string]FcInfixOptPrecedence{
	"+": PrecAddition,
	"-": PrecAddition,
	"*": PrecMultiplication,
	"/": PrecMultiplication,
	"^": PrecExponentiation,
}

// All Unary operators have higher Precedence than infix operators
var UnaryPrecedence = map[string]FcInfixOptPrecedence{
	"-": PrecUnary,
}
