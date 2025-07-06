// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Litex email: <litexlang@outlook.com>
// Litex website: https://litexlang.org
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_global

func IsKeySymbol(name string) bool {
	_, ok := symbolSet[name]
	return ok
}

func IsBuiltinInfixRelaPropSymbol(op string) bool {
	return op == KeySymbolEqual || op == KeySymbolLess || op == KeySymbolGreater || op == KeySymbolEqualEqual || op == KeySymbolNotEqual || op == KeywordIn || op == KeySymbolLargerEqual || op == KeySymbolLessEqual
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
	PrecModulo                              // %
)

var BuiltinOptPrecedenceMap = map[string]BuiltinOptPrecedence{
	KeySymbolPlus:    PrecAddition,
	KeySymbolMinus:   PrecAddition,
	KeySymbolStar:    PrecMultiplication,
	KeySymbolSlash:   PrecMultiplication,
	KeySymbolPower:   PrecExponentiation,
	KeySymbolPercent: PrecModulo,
}

// All Unary operators have higher Precedence than infix operators
// TODO 未来有其他的unary opt的时候，需要修改 strSliceCursor.unaryOptFc
// var UnaryPrecedence = map[string]BuiltinOptPrecedence{
// 	KeySymbolMinus: PrecUnary,
// }

func IsKeyword(s string) bool {
	_, ok := BuiltinKeywordsSet[s]
	return ok
}

func GetKeySymbol(inputString string, start int) string {
	if start < 0 || start >= len(inputString) {
		return ""
	}

	// 先检查 3 字符符号
	// if start+3 <= len(inputString) {
	// 	candidate := inputString[start : start+3]
	// 	if _, ok := symbolSet[candidate]; ok {
	// 		return candidate
	// 	}
	// }

	// 再检查 2 字符符号
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
