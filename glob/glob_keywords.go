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
// Litex website: https://litexlang.com
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_global

// ! 每次新增keyword的时候，要记住把它往isKeyword里加
const (
	KeywordSet    = "set"
	KeywordForall = "forall"
	KeywordDom    = "dom" // 这是一种语法糖。本质上只要在定义集合的时候写了对集合的要求，那dom就不必要的，因为dom本质上是 ”临时添加新的要求"
	// KeywordThen                 = "then"
	KeywordObj       = "obj"
	KeywordHave      = "have"
	KeywordFn        = "fn"
	KeywordProp      = "prop"
	KeywordKnow      = "know"
	KeywordExist     = "exist"
	KeywordSt        = "st"
	KeywordExistProp = "exist_prop"
	KeywordClaim     = "claim"
	KeywordProve     = "prove"
	KeywordImport    = "import"
	KeywordNot       = "not"
	// KeywordIff                  = "iff"
	KeywordProveByContradiction   = "prove_by_contradiction"
	KeywordProveInEachCase        = "prove_in_each_case" // 必要：和or一起使用
	KeywordOr                     = "or"
	KeywordProveIsCommutativeProp = "prove_is_commutative_prop" // 这个 keyword是真的在工作的
	KeywordNatural                = "N"                         // e.g. 0
	KeywordInteger                = "Z"                         // e.g. -1
	KeywordRational               = "Q"                         // e.g. -1.1
	KeywordReal                   = "R"                         // e.g. pi
	KeywordComplex                = "C"                         // e.g. 1+i
	KeywordIn                     = "in"
	// KeywordProveByMathInduction           = "prove_by_math_induction"
	KeywordAs           = "as" // 用在 import xxx as ??? 了
	KeywordLen          = "len"
	KeywordFiniteSet    = "finite_set"
	KeywordProveByEnum  = "prove_by_enum" // syntax connecting forall and finite_set
	KeywordItemExistsIn = "item_exists_in"

	// WARNING: TODO 我不知道这三个集合是什么用途
	// TODO: 需要有他们的对应关系
	KeywordSetDefinedByReplacement        = "set_defined_by_replacement"    // 这是一个函数，返回一个集合，而不是一个prop
	KeywordExistPropPreImageByReplacement = "obj_exist_as_preimage_of_prop" //"exist_prop_preimage_by_replacement"
	KeywordExistFnPreImageByReplacement   = "obj_exist_as_preimage_of_fn"   // "exist_fn_preimage_by_replacement"

	KeywordFnTemplate = "fn_template"

	KeywordNPos  = "N_pos"
	KeywordLet   = "let"
	KeywordClear = "clear"

	KeywordProveByInduction = "prove_by_induction"

	KeywordLift        = "lift"
	KeywordNonEmptySet = "nonempty_set"

	KeywordWhen = "when"

	KeywordProveIsTransitiveProp = "prove_is_transitive_prop"

	KeywordProveInRange = "prove_in_range"

	KeywordAlgo   = "algo"
	KeywordReturn = "return"
	KeywordIf     = "if"
)

var BuiltinKeywordsSet map[string]struct{} = map[string]struct{}{
	KeywordSet:    {},
	KeywordForall: {},
	KeywordDom:    {},
	// KeywordThen:                 {},
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
	// KeywordIff:                  {},
	KeywordExist:                  {},
	KeywordProveIsCommutativeProp: {},
	KeywordOr:                     {},
	KeywordNatural:                {},
	KeywordInteger:                {},
	KeywordRational:               {},
	KeywordReal:                   {},
	KeywordIn:                     {},
	// KeywordProveByMathInduction:           {},
	KeywordComplex:                        {},
	KeywordAs:                             {},
	KeywordLen:                            {},
	KeywordFiniteSet:                      {},
	KeywordProveByEnum:                    {},
	KeywordItemExistsIn:                   {},
	KeywordSetDefinedByReplacement:        {},
	KeywordExistPropPreImageByReplacement: {},
	KeywordExistFnPreImageByReplacement:   {},
	KeywordFnTemplate:                     {},
	KeywordNPos:                           {},
	KeywordLet:                            {},
	KeywordClear:                          {},
	// KeywordExistSetByAxiomOfReplacement:   {},

	KeywordProveIsTransitiveProp: {},

	KeywordProveByInduction: {},

	KeywordLift:        {},
	KeywordNonEmptySet: {},

	KeywordWhen: {},

	KeywordAlgo:   {},
	KeywordReturn: {},
	KeywordIf:     {},
}

const (
	KeySymbolColon        = ":"
	KeySymbolLeftBrace    = "("
	KeySymbolRightBrace   = ")"
	KeySymbolComma        = ","
	KeySymbolDollar       = "$"
	KeySymbolEqual        = "="
	KeySymbolSlash        = "/"
	KeySymbolPlus         = "+"
	KeySymbolMinus        = "-"
	KeySymbolStar         = "*"
	KeySymbolPower        = "^"
	KeySymbolLess         = "<"
	KeySymbolGreater      = ">"
	KeySymbolDot          = "."
	KeySymbolColonColon   = "::"
	KeySymbolNotEqual     = "!=" // 在parse就立刻变成 not =，exec里没有对它的处理
	KeySymbolDoubleQuote  = "\""
	KeySymbolHash         = "#"
	KeySymbolLargerEqual  = ">="
	KeySymbolLessEqual    = "<="
	KeySymbolEqualEqual   = "==" // check fn equal. TODO: 要调整语义
	KeySymbolPercent      = "%"  // prove: 2 % 2 = 0 的时候打印有问题，不知道为什么
	KeySymbolLeftBracket  = "["
	KeySymbolRightBracket = "]"
	// KeySymbolColonEqual   = ":="
	KeySymbolLeftCurly  = "{"
	KeySymbolRightCurly = "}"
	KeySymbolAt         = "@"
	KeySymbolRightArrow = "=>"

	KeySymbolSemiColon  = ";"
	KeySymbolEquivalent = "<=>"
	KeySymbolBackSlash  = "\\"
	// KeySymbolQuestionMark = "?"
)

// 最多双字符，或者单字符，否则parser的逻辑 GetKeySymbol 有问题
var symbolSet map[string]struct{} = map[string]struct{}{
	KeySymbolEqualEqual:  {}, // "=="
	KeySymbolLargerEqual: {}, // ">="
	KeySymbolLessEqual:   {}, // "<="
	KeySymbolNotEqual:    {}, // "!="
	KeySymbolColonColon:  {}, // "::"
	// KeySymbolColonEqual:   {}, // ":="
	KeySymbolPower:        {}, // "^"
	KeySymbolColon:        {}, // ":"
	KeySymbolComma:        {}, // ","
	KeySymbolDot:          {}, // "."
	KeySymbolDollar:       {}, // "$"
	KeySymbolDoubleQuote:  {}, // "\""
	KeySymbolEqual:        {}, // "="
	KeySymbolGreater:      {}, // ">"
	KeySymbolHash:         {}, // "#"
	KeySymbolLeftBrace:    {}, // "("
	KeySymbolLess:         {}, // "<"
	KeySymbolMinus:        {}, // "-"
	KeySymbolPlus:         {}, // "+"
	KeySymbolRightBrace:   {}, // ")"
	KeySymbolSlash:        {}, // "/"
	KeySymbolStar:         {}, // "*"
	KeySymbolPercent:      {}, // "%"
	KeySymbolLeftBracket:  {}, // "["
	KeySymbolRightBracket: {}, // "]"
	KeySymbolLeftCurly:    {}, // "{"
	KeySymbolRightCurly:   {}, // "}"
	KeySymbolAt:           {}, // "@"
	KeySymbolRightArrow:   {}, // "=>"
	KeySymbolSemiColon:    {}, // ";"
	KeySymbolEquivalent:   {}, // "<=>"
	KeySymbolBackSlash:    {},
	// KeySymbolQuestionMark: {}, // "?"
}

var BuiltinKeywordKeySymbolCanBeFcAtomNameSet map[string]struct{} = map[string]struct{}{
	KeywordObj:           {},
	KeywordSet:           {},
	KeywordNatural:       {},
	KeywordInteger:       {},
	KeywordRational:      {},
	KeywordReal:          {},
	KeywordComplex:       {},
	KeywordAs:            {},
	KeywordIn:            {},
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
	// KeySymbolColonEqual:                   {},
	KeySymbolEqualEqual:                   {},
	KeySymbolPercent:                      {}, // prove: 2 % 2 = 0 的时候打印有问题，不知道为什么
	KeySymbolLeftBracket:                  {},
	KeySymbolRightBracket:                 {},
	KeywordFiniteSet:                      {},
	KeywordItemExistsIn:                   {},
	KeywordSetDefinedByReplacement:        {},
	KeywordExistPropPreImageByReplacement: {},
	KeywordExistFnPreImageByReplacement:   {},
	TupleFcFnHead:                         {},
	KeywordLen:                            {},
	KeywordNPos:                           {},
	KeywordNonEmptySet:                    {},
}

func IsBuiltinKeywordKeySymbolCanBeFcAtomName(name string) bool {
	_, ok := BuiltinKeywordKeySymbolCanBeFcAtomNameSet[name]
	return ok
}

func IsBuiltinKeywordOrBuiltinSymbolOrNumber(name string) bool {
	if IsKeyword(name) || IsKeySymbol(name) || (name[0] >= '0' && name[0] <= '9') {
		return true
	}
	return false
}

var BuiltinObjKeywordSet map[string]struct{} = map[string]struct{}{
	KeywordNatural:   {},
	KeywordInteger:   {},
	KeywordRational:  {},
	KeywordReal:      {},
	KeywordComplex:   {},
	KeywordFiniteSet: {},
	KeywordSet:       {},
	KeywordNPos:      {},
}

var AddMinusStarSet map[string]struct{} = map[string]struct{}{
	KeySymbolPlus:  {},
	KeySymbolMinus: {},
	KeySymbolStar:  {},
}

const LeftIsEqual0RightIsPositive = "__leftIsEqual0RightIsPositive__"
const LeftIsNegativeRightIsInteger = "__leftIsNegativeRightIsInteger__"
const LastTwoObjectsAreEqual = "__last_two_objects_are_equal__"

var builtinPropObjNames = map[string]struct{}{
	LeftIsEqual0RightIsPositive:  {},
	LeftIsNegativeRightIsInteger: {},
	LastTwoObjectsAreEqual:       {},
}
