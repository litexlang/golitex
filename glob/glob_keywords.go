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

// ! 每次新增keyword的时候，要记住把它往isKeyword里加
const (
	KeywordSet                  = "set"
	KeywordForall               = "forall"
	KeywordDom                  = "dom" // 这是一种语法糖。本质上只要在定义集合的时候写了对集合的要求，那dom就不必要的，因为dom本质上是 ”临时添加新的要求"
	KeywordThen                 = "then"
	KeywordObj                  = "obj"
	KeywordHave                 = "have"
	KeywordFn                   = "fn"
	KeywordProp                 = "prop"
	KeywordKnow                 = "know"
	KeywordExist                = "exist"
	KeywordSt                   = "st"
	KeywordExistProp            = "exist_prop"
	KeywordClaim                = "claim"
	KeywordProve                = "prove"
	KeywordImport               = "import"
	KeywordNot                  = "not"
	KeywordIff                  = "iff"
	KeywordProveByContradiction = "prove_by_contradiction"
	KeywordProveInEachCase      = "prove_in_each_case" // 必要：和or一起使用
	KeywordAnd                  = "and"
	KeywordOr                   = "or"
	KeywordCommutativeProp      = "commutative_prop"
	// KeywordCommutativeFn        = "commutative_fn" // must-have: 否则 a+b=b+a不能验证
	KeywordAssociativeFn        = "associative_fn" // must-have: 否则 a+1+1=a+2不能验证 // 我觉得暂时不考虑不较好，比较associative的自然数之类的都默认是对的了
	KeywordNatural              = "N"              // e.g. 0
	KeywordInt                  = "Z"              // e.g. -1
	KeywordRational             = "Q"              // e.g. -1.1
	KeywordReal                 = "R"              // e.g. pi
	KeywordComplex              = "C"              // e.g. 1+i
	KeywordImaginary            = "i"              // e.g. i
	KeywordIn                   = "in"
	KeywordProveByMathInduction = "prove_by_math_induction"
	// KeywordProveOr              = "prove_or"
	KeywordSuppose = "suppose"
	KeywordWith    = "with"
	KeywordAs      = "as" // as a fn_template。这非常难以实现，尤其是出现 fn 理论上作用在M上，现在是作用在返回值是M的函数上时做推理，非常困难，需要最后实现而不是现在

	// KeywordFnSet                  = "fn_set" // Syntax sugar for fn setName(params paramsSet)  = {z z_set_name(params) | properties(z, params)}
	KeywordLen                    = "len"
	KeywordIsIndexableSet         = "is_indexable_set"
	KeywordIsFiniteSet            = "is_finite_set"
	KeywordProveForallIteratively = "prove_iteratively" // syntax connecting forall and finite_set
	KeywordFnTemplate             = "fn_template"
	KeywordStruct                 = "struct"

	// KeywordSubsetOf = "subset_of" // though this can be defined by forall, it's still useful to have it as a keyword
	// TODO
	// a syntax connecting or and finite_set
	// KeywordEnum = "enum"

	KeywordImportGlobally    = "import_globally"
	KeywordHaveByReplacement = "have_by_replacement"
	// KeywordLastTwoObjectsAreEqual = "last_two_objects_are_equal"
)

var BuiltinKeywordsSet map[string]struct{} = map[string]struct{}{
	KeywordSet:                  {},
	KeywordForall:               {},
	KeywordDom:                  {},
	KeywordThen:                 {},
	KeywordObj:                  {},
	KeywordHave:                 {},
	KeywordFn:                   {},
	KeywordProp:                 {},
	KeywordKnow:                 {},
	KeywordExistProp:            {},
	KeywordSt:                   {},
	KeywordClaim:                {},
	KeywordProve:                {},
	KeywordImport:               {},
	KeywordNot:                  {},
	KeywordProveByContradiction: {},
	KeywordProveInEachCase:      {},
	KeywordIff:                  {},
	KeywordExist:                {},
	KeywordCommutativeProp:      {},
	// KeywordCommutativeFn:        {},
	KeywordAssociativeFn:        {},
	KeywordAnd:                  {},
	KeywordOr:                   {},
	KeywordNatural:              {},
	KeywordInt:                  {},
	KeywordRational:             {},
	KeywordReal:                 {},
	KeywordIn:                   {},
	KeywordProveByMathInduction: {},
	// KeywordProveOr:                {},
	KeywordSuppose:   {},
	KeywordWith:      {},
	KeywordComplex:   {},
	KeywordImaginary: {},
	KeywordAs:        {},
	// KeywordFnSet:                  {},
	KeywordLen:                    {},
	KeywordIsIndexableSet:         {},
	KeywordIsFiniteSet:            {},
	KeywordProveForallIteratively: {},
	KeywordFnTemplate:             {},
	KeywordStruct:                 {},
	// KeywordSubsetOf:               {},
	// KeywordEnum:              {},
	KeywordImportGlobally:    {},
	KeywordHaveByReplacement: {},
}

const (
	// Builtin Symbols
	KeySymbolColon      = ":"
	KeySymbolLeftBrace  = "("
	KeySymbolRightBrace = ")"
	KeySymbolComma      = ","
	KeySymbolDollar     = "$"
	KeySymbolEqual      = "="
	KeySymbolSlash      = "/"
	KeySymbolPlus       = "+"
	KeySymbolMinus      = "-"
	KeySymbolStar       = "*"
	KeySymbolPower      = "^"
	KeySymbolLess       = "<"
	KeySymbolGreater    = ">"
	KeySymbolExclaim    = "!"
	// KeySymbolPipe       = "|"
	// KeySymbolTilde      = "~"
	// KeySymbolAnd        = "&"
	KeySymbolBackslash  = "\\"
	KeySymbolDot        = "."
	KeySymbolColonColon = "::"
	// KeySymbolPlusPlus   = "++"
	// KeySymbolMinusMinus = "--"
	// KeySymbolAndAnd     = "&&"
	// KeySymbolPipePipe   = "||"
	KeySymbolNotEqual = "!=" // 在parse就立刻变成 not =，exec里没有对它的处理
	// KeySymbolQuestion   = "?"
	// KeySymbolStarStar    = "**"
	KeySymbolDoubleQuote = "\""
	// KeySymbolSingleQuote            = "'"
	// KeySymbolBacktick = "`"
	// KeySymbolEqualGreaterEqual      = "=>"
	// KeySymbolMinusGreaterRightArrow = "->"
	// KeySymbolSemicolon              = ";"
	KeySymbolHash = "#"
	// KeySymbolAt          = "@"
	KeySymbolLargerEqual = ">="
	KeySymbolLessEqual   = "<="
	// KeySymbolEquivalent  = "<=>"
	// It's possible for me to overload the meaning of "=" to mean "set equal", but I don't want to do that(I do not want to overload the meaning of "=" too much, which can be very tiring for future maintainers and make confusions), so I use a new keyword
	KeySymbolEqualEqual = "==" // check fn equal. TODO: 要调整语义
	// KeySymbolEqualEqualEqual = "===" // check set equal. TODO: 要调整语义
	// KeySymbolGreaterGreater = ">>"
	// KeySymbolLessLess     = "<<"
	KeySymbolPercent      = "%" // prove: 2 % 2 = 0 的时候打印有问题，不知道为什么
	KeySymbolLeftBracket  = "["
	KeySymbolRightBracket = "]"
	KeySymbolColonEqual   = ":="
	KeySymbolLeftCurly    = "{"
	KeySymbolRightCurly   = "}"
)

// 最多双字符，或者单字符，否则parser的逻辑 GetKeySymbol 有问题
var symbolSet map[string]struct{} = map[string]struct{}{
	// 双字符符号（长度 2）
	// KeySymbolAndAnd:     {}, // "&&"
	KeySymbolEqualEqual: {}, // "=="
	// KeySymbolEqualGreaterEqual:      {}, // "=>"
	KeySymbolLargerEqual: {}, // ">="
	KeySymbolLessEqual:   {}, // "<="
	// KeySymbolMinusGreaterRightArrow: {}, // "->"
	KeySymbolNotEqual: {}, // "!="
	// KeySymbolPipePipe:   {}, // "||"
	// KeySymbolPlusPlus:   {}, // "++"
	// KeySymbolMinusMinus: {}, // "--"
	// KeySymbolStarStar:               {}, // "**"
	KeySymbolColonColon: {}, // "::"
	KeySymbolColonEqual: {}, // ":="
	// 单字符符号（长度 1）
	// KeySymbolAt:          {}, // "@"
	KeySymbolBackslash: {}, // "\\"
	// KeySymbolBacktick:    {}, // "`"
	KeySymbolPower:       {}, // "^"
	KeySymbolColon:       {}, // ":"
	KeySymbolComma:       {}, // ","
	KeySymbolDot:         {}, // "."
	KeySymbolDollar:      {}, // "$"
	KeySymbolDoubleQuote: {}, // "\""
	KeySymbolEqual:       {}, // "="
	KeySymbolExclaim:     {}, // "!"
	KeySymbolGreater:     {}, // ">"
	KeySymbolHash:        {}, // "#"
	// KeySymbolLeftBracket: {}, // "["
	// KeySymbolLeftCurly:       {}, // "{"
	KeySymbolLeftBrace: {}, // "("
	KeySymbolLess:      {}, // "<"
	KeySymbolMinus:     {}, // "-"
	// KeySymbolPipe:      {}, // "|"
	KeySymbolPlus: {}, // "+"
	// KeySymbolQuestion: {}, // "?"
	// KeySymbolRightBracket: {}, // "]"
	// KeySymbolRightCurly:      {}, // "}"
	KeySymbolRightBrace: {}, // ")"
	// KeySymbolSemicolon:        {}, // ";"
	// KeySymbolSingleQuote: {}, // "'"
	KeySymbolSlash: {}, // "/"
	KeySymbolStar:  {}, // "*"
	// KeySymbolTilde: {}, // "~"
	// KeySymbolAnd: {}, // "&"
	// KeySymbolEquivalent:  {}, // "<=>"
	// KeySymbolEqualEqualEqual: {}, // "==="
	// KeySymbolGreaterGreater: {}, // ">>"
	// KeySymbolLessLess:     {}, // "<<"
	KeySymbolPercent:      {}, // "%"
	KeySymbolLeftBracket:  {}, // "["
	KeySymbolRightBracket: {}, // "]"
	KeySymbolLeftCurly:    {}, // "{"
	KeySymbolRightCurly:   {}, // "}"
}

var BuiltinKeywordKeySymbolCanBeFcAtomNameSet map[string]struct{} = map[string]struct{}{
	KeywordObj:       {},
	KeywordSet:       {},
	KeywordNatural:   {},
	KeywordInt:       {},
	KeywordRational:  {},
	KeywordReal:      {},
	KeywordComplex:   {},
	KeywordImaginary: {},
	KeywordAs:        {},
	KeywordIn:        {},
	// KeywordSubsetOf:      {},
	KeySymbolEqual:       {},
	KeySymbolSlash:       {},
	KeySymbolPlus:        {},
	KeySymbolMinus:       {},
	KeySymbolStar:        {},
	KeySymbolPower:       {},
	KeySymbolLess:        {},
	KeySymbolGreater:     {},
	KeySymbolLargerEqual: {},
	KeySymbolLessEqual:   {},
	KeySymbolNotEqual:    {},
	KeySymbolColonEqual:  {},
	// KeySymbolEquivalent:  {},
	KeySymbolEqualEqual: {},
	// KeySymbolEqualEqualEqual: {},
	KeySymbolPercent:      {}, // prove: 2 % 2 = 0 的时候打印有问题，不知道为什么
	KeySymbolLeftBracket:  {},
	KeySymbolRightBracket: {},

	KeywordCommutativeProp: {},
	KeywordIsFiniteSet:     {},
	// KeySymbolSemicolon:     {},
}

func IsBuiltinKeywordKeySymbolCanBeFcAtomName(name string) bool {
	// if IsKeyword(name) || IsKeySymbol(name) {
	_, ok := BuiltinKeywordKeySymbolCanBeFcAtomNameSet[name]
	return ok
	// }
	// return false
}

// func IsBuiltinKeywordKeySymbol_NeverBeFcAtom(name string) bool {
// 	if IsKeyword(name) || IsKeySymbol(name) {
// 		_, ok := BuiltinKeywordKeySymbolCanBeFcAtomNameSet[name]
// 		return !ok
// 	}
// 	return false
// }

func IsBuiltinKeywordOrBuiltinSymbolOrNumber(name string) bool {
	if IsKeyword(name) || IsKeySymbol(name) || (name[0] >= '0' && name[0] <= '9') {
		return true
	}
	return false
}

var BuiltinObjKeywordSet map[string]struct{} = map[string]struct{}{
	KeywordNatural:   {},
	KeywordInt:       {},
	KeywordRational:  {},
	KeywordReal:      {},
	KeywordComplex:   {},
	KeywordImaginary: {},
}
