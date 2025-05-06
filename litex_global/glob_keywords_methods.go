// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Contact the development team: <litexlang@outlook.com>
// Visit litexlang.org and https://github.com/litexlang/golitex for more info.

package litex_global

func IsKeySymbol(name string) bool {
	_, ok := symbolSet[name]
	return ok
}

func IsBuiltinInfixRelaProp(op string) bool {
	return op == "=" || op == "<" || op == ">" || op == "<=" || op == ">=" || op == "==" || op == "!=" || op == "in" || op == KeywordCommutative || op == KeywordAssociative
}

func IsBuiltinNumberInfixRelaProp(op string) bool {
	return op == "<" || op == ">" || op == "<=" || op == ">=" || op == "=" || op == "==" || op == "!="
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

func IsKeyword(s string) bool {
	_, ok := keywordsSet[s]
	return ok
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

func IsKeySymbolUnaryFn(name string) bool {
	_, ok := UnaryPrecedence[name]
	return ok
}

func IsKeywordSymbolUnaryAndInfixAtTheSameTime(name string) bool {
	_, ok := BuiltinOptPrecedenceMap[name]
	_, ok2 := UnaryPrecedence[name]
	return ok && ok2
}

func IsBuiltinUnaryOpt(name string) bool {
	_, ok := UnaryPrecedence[name]
	return ok
}

var notFcAtomNameSet = map[string]struct{}{
	// 常规关键字
	KeywordForall: {},
	// KeywordWhen:     {},
	KeywordDom:      {},
	KeywordThen:     {},
	KeywordExistObj: {},
	KeywordSt:       {},
	// KeywordConstructorProp:      {},
	KeywordClaim:   {},
	KeywordProve:   {},
	KeywordPub:     {},
	KeywordImport:  {},
	KeywordPackage: {},
	KeywordNot:     {},
	// KeywordAxiom:                {},
	KeywordProveByContradiction: {},
	// KeywordThm:                  {},
	KeywordIff:   {},
	KeywordExist: {},
}

func IsKwThatCanNeverBeFcName(s string) bool {
	_, ok := notFcAtomNameSet[s]
	return ok || IsKeySymbol(s)
}
