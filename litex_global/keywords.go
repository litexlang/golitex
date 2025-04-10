package litex_global

const ScopeIndent = "    "

// 每次新增keyword的时候，要记住把它往isKeyword里加
const (
	KeywordInterface            = "interface"
	KeywordType                 = "type"
	KeywordSet                  = "set"
	KeywordForall               = "forall"
	KeywordWhen                 = "when"
	KeywordDom                  = "dom" // 必须存在，因为有时候只有要求没then
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
	KeywordThm                  = "thm" // syntax sugar for: prop + prove
	// KeywordSelf                 = "self" // return value of a function; refer to an instance of the type or set we are defining
	KeywordIff = "iff"

	// Syntax and Semantics Sugar
	KeywordCommutative = "commutative"
	KeywordAssociative = "associative"

	// Builtin Types
	KeywordNat      = "nat"      // e.g. 0
	KeywordInt      = "int"      // e.g. -1
	KeywordRational = "rational" // e.g. -1.1
	KeywordReal     = "real"     // e.g. pi

	// Builtin Functions
	KeywordIs   = "is"
	KeywordIn   = "in"
	KeyWordFrac = "frac"

	// 下面是 内置函数名

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

const (
	// Builtin Symbols
	KeySymbolColon                  = ":"
	KeySymbolLeftBracket            = "["
	KeySymbolRightBracket           = "]"
	KeySymbolLeftParen              = "("
	KeySymbolRightParen             = ")"
	KeySymbolComma                  = ","
	KeySymbolDollar                 = "$"
	KeySymbolEqual                  = "="
	KeySymbolSlash                  = "/"
	KeySymbolPlus                   = "+"
	KeySymbolMinus                  = "-"
	KeySymbolStar                   = "*"
	KeySymbolCaret                  = "^"
	KeySymbolLess                   = "<"
	KeySymbolGreater                = ">"
	KeySymbolExclaim                = "!"
	KeySymbolPipe                   = "|"
	KeySymbolTilde                  = "~"
	KeySymbolAnd                    = "&"
	KeySymbolDot                    = "."
	KeySymbolColonColon             = "::"
	KeySymbolPlusPlus               = "++"
	KeySymbolMinusMinus             = "--"
	KeySymbolAndAnd                 = "&&"
	KeySymbolPipePipe               = "||"
	KeySymbolEqualEqual             = "=="
	KeySymbolNotEqual               = "!="
	KeySymbolBackslash              = "\\"
	KeySymbolQuestion               = "?"
	KeySymbolStarStar               = "**"
	KeySymbolDoubleQuote            = "\""
	KeySymbolSingleQuote            = "'"
	KeySymbolBacktick               = "`"
	KeySymbolEqualGreaterRightArrow = "=>"
	KeySymbolMinusGreaterRightArrow = "->"
	KeySymbolSemicolon              = ";"
	KeySymbolLeftCurly              = "{"
	KeySymbolRightCurly             = "}"
	KeySymbolHash                   = "#"
	KeySymbolAt                     = "@"
	//! 每次引入新的Symbol，要往getBuiltinSymbol里加东西
)

// 加prefix的好处：如果要执行一个uniFact，那可以直接执行，不用担心检查的时候用到同名的外界obj的事实:因为自由变量全是#开头的，而用户定义的变量没有#开头
// 在编译时加入prefix的好处：1. 加prefix这个事情是用不到runtime信息的，所以在编译时可以这么干 2. 确实要比运行时方便：运行时很多地方都需要用到prefix，不如在一开始让所有的uniFact全部加上#，而不是“有的时候用#，有时候不用，这样容易错”
const UniParamPrefix = KeySymbolHash

func IsKeySymbol(name string) bool {
	_, ok := symbolSet[name]
	return ok
}

func IsKeySymbolRelaProp(op string) bool {
	return op == "<" || op == ">" || op == "<=" || op == ">=" || op == "=" || op == "==" || op == "!=" || op == "in"
}

func IsKeySymbolRelaFn(op string) bool {
	for key := range BuiltinOptPrecedenceMap {
		if op == key {
			return true
		}
	}
	return false
}

type BuiltinOptPrecedence int

// TODO: implement other operators. How logical operators work is also not implemented
const (
	PrecLowest         BuiltinOptPrecedence = iota
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

var BuiltinOptPrecedenceMap = map[string]BuiltinOptPrecedence{
	KeySymbolPlus:  PrecAddition,
	KeySymbolMinus: PrecAddition,
	KeySymbolStar:  PrecMultiplication,
	KeySymbolSlash: PrecMultiplication,
	KeySymbolCaret: PrecExponentiation,
}

// All Unary operators have higher Precedence than infix operators
var UnaryPrecedence = map[string]BuiltinOptPrecedence{
	KeySymbolMinus: PrecUnary,
}

var Keywords = []string{
	// 常规关键字
	KeywordInterface,
	KeywordType,
	KeywordSet,
	KeywordForall,
	KeywordWhen,
	KeywordDom,
	KeywordThen,
	KeywordObj,
	KeywordFn,
	KeywordProp,
	KeywordKnow,
	KeywordExistProp,
	KeywordHave,
	KeywordClaim,
	KeywordProve,
	KeywordPub,
	KeywordImport,
	KeywordPackage,
	KeywordNot,
	KeywordImpl,
	KeywordAs,
	KeywordAxiom,
	KeywordProveByContradiction,
	KeywordThm,
	// KeywordSelf,
	KeywordIff,

	// 语法糖
	KeywordCommutative,
	KeywordAssociative,

	// 内置类型
	KeywordNat,
	KeywordInt,
	KeywordRational,
	KeywordReal,

	// 内置函数
	KeywordIs,
	KeywordIn,

	// 运算符函数
	Keyword__Div__,
	Keyword__Add__,
	Keyword__Sub__,
	Keyword__Mul__,
	Keyword__Xor__,
	Keyword__LT__,
	Keyword__GT__,
	Keyword__Exclamation__,
	Keyword__Or__,
	Keyword__And__,
	Keyword__AddAdd__,
	Keyword__SubSub__,
	Keyword__AndAnd__,
	Keyword__PipePipe__,
	Keyword__EqEq__,
	Keyword__NE__,
	Keyword__Pow__,
	Keyword__LT_EQ__,
	Keyword__GT_EQ__,
	Keyword__Union__,
	Keyword__Intersection__,
	Keyword__SubsetEq__,
	Keyword__SupsetEq__,
	Keyword__Subset__,
	Keyword__Supset__,
	Keyword__SubGT__,
	Keyword__EqGT__,
}

func IsKeyword(s string) bool {
	for _, kw := range Keywords {
		if s == kw {
			return true
		}
	}
	return false
}

func GetKeySymbol(inputString string, start int) string {
	if start < 0 || start >= len(inputString) {
		return ""
	}

	// 先检查 2 字符符号
	if start+2 <= len(inputString) {
		candidate := inputString[start : start+2]
		if _, ok := symbolSet[candidate]; ok {
			return candidate
		}
	}

	// 再检查 1 字符符号
	if start+1 <= len(inputString) {
		candidate := inputString[start : start+1]
		if _, ok := symbolSet[candidate]; ok {
			return candidate
		}
	}

	return ""
}

var symbolSet map[string]struct{} = initSymbolSet() // 存储所有符号

func initSymbolSet() map[string]struct{} {
	var KeySymbolSlice = []string{
		// 双字符符号（长度 2）
		KeySymbolAndAnd,                 // "&&"
		KeySymbolEqualEqual,             // "=="
		KeySymbolEqualGreaterRightArrow, // "=>"
		KeySymbolMinusGreaterRightArrow, // "->"
		KeySymbolNotEqual,               // "!="
		KeySymbolPipePipe,               // "||"
		KeySymbolPlusPlus,               // "++"
		KeySymbolMinusMinus,             // "--"
		KeySymbolStarStar,               // "**"
		KeySymbolColonColon,             // "::"

		// 单字符符号（长度 1）
		KeySymbolAt,           // "@"
		KeySymbolBackslash,    // "\\"
		KeySymbolBacktick,     // "`"
		KeySymbolCaret,        // "^"
		KeySymbolColon,        // ":"
		KeySymbolComma,        // ","
		KeySymbolDot,          // "."
		KeySymbolDollar,       // "$"
		KeySymbolDoubleQuote,  // "\""
		KeySymbolEqual,        // "="
		KeySymbolExclaim,      // "!"
		KeySymbolGreater,      // ">"
		KeySymbolHash,         // "#"
		KeySymbolLeftBracket,  // "["
		KeySymbolLeftCurly,    // "{"
		KeySymbolLeftParen,    // "("
		KeySymbolLess,         // "<"
		KeySymbolMinus,        // "-"
		KeySymbolPipe,         // "|"
		KeySymbolPlus,         // "+"
		KeySymbolQuestion,     // "?"
		KeySymbolRightBracket, // "]"
		KeySymbolRightCurly,   // "}"
		KeySymbolRightParen,   // ")"
		KeySymbolSemicolon,    // ";"
		KeySymbolSingleQuote,  // "'"
		KeySymbolSlash,        // "/"
		KeySymbolStar,         // "*"
		KeySymbolTilde,        // "~"
		KeySymbolAnd,          // "&"
	}

	symbolSet := make(map[string]struct{})
	for _, symbol := range KeySymbolSlice {
		symbolSet[symbol] = struct{}{}
	}
	return symbolSet
}
