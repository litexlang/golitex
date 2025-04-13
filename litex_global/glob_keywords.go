/*
 * Copyright 2024 Jiachen Shen.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Original Author: Jiachen Shen (malloc_realloc_calloc@outlook.com)
 * Visit litexlang.org and https://github.com/litexlang/golitex for more information.
 */

package litex_global

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
	KeywordNatural  = "nat"      // e.g. 0
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
	KeySymbolLeftBrace              = "("
	KeySymbolRightBrace             = ")"
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
	KeySymbolLargerEqual            = ">="
	KeySymbolLessEqual              = "<="
	//! 每次引入新的Symbol，要往getBuiltinSymbol里加东西
)

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
// TODO 未来有其他的unary opt的时候，需要修改 strSliceCursor.unaryOptFc
var UnaryPrecedence = map[string]BuiltinOptPrecedence{
	KeySymbolMinus: PrecUnary,
}

var keywordsSet map[string]struct{} = initKeywordSet() // 存储所有关键字

func IsKeyword(s string) bool {
	_, ok := keywordsSet[s]
	return ok
}

func initKeywordSet() map[string]struct{} {
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
		KeywordNatural,
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

	keywordSet := make(map[string]struct{})
	for _, keyword := range Keywords {
		keywordSet[keyword] = struct{}{}
	}
	return keywordSet
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
		KeySymbolLeftBrace,    // "("
		KeySymbolLess,         // "<"
		KeySymbolMinus,        // "-"
		KeySymbolPipe,         // "|"
		KeySymbolPlus,         // "+"
		KeySymbolQuestion,     // "?"
		KeySymbolRightBracket, // "]"
		KeySymbolRightCurly,   // "}"
		KeySymbolRightBrace,   // ")"
		KeySymbolSemicolon,    // ";"
		KeySymbolSingleQuote,  // "'"
		KeySymbolSlash,        // "/"
		KeySymbolStar,         // "*"
		KeySymbolTilde,        // "~"
		KeySymbolAnd,          // "&"
		KeySymbolLargerEqual,  // ">="
		KeySymbolLessEqual,    // "<="
	}

	symbolSet := make(map[string]struct{})
	for _, symbol := range KeySymbolSlice {
		symbolSet[symbol] = struct{}{}
	}
	return symbolSet
}

func IsKeySymbolUniFn(name string) bool {
	_, ok := UnaryPrecedence[name]
	return ok
}

func IsKeywordSymbolUnaryAndInfixAtTheSameTime(name string) bool {
	_, ok := BuiltinOptPrecedenceMap[name]
	_, ok2 := UnaryPrecedence[name]
	return ok && ok2
}
