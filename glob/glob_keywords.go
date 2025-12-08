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
	// KeywordObj       = "obj"
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
	KeywordIn                     = "in"
	// KeywordProveByMathInduction           = "prove_by_math_induction"
	KeywordAs           = "as" // 用在 import xxx as ??? 了
	KeywordCount        = "count"
	KeywordFiniteSet    = "finite_set"
	KeywordProveByEnum  = "prove_by_enum" // syntax connecting forall and finite_set
	KeywordItemExistsIn = "item_exists_in"

	KeywordFnTemplate = "fn_template"

	KeywordNPos  = "N_pos"
	KeywordLet   = "let"
	KeywordClear = "clear"

	KeywordProveByInduction = "prove_by_induction"

	KeywordLift        = "lift"
	KeywordNonEmptySet = "nonempty_set"

	KeywordProveIsTransitiveProp = "prove_is_transitive_prop"

	KeywordProveInRangeSet = "prove_in_range_set"
	KeywordProveInRange    = "prove_in_range"

	KeywordAlgo   = "algo"
	KeywordReturn = "return"
	KeywordIf     = "if"
	KeywordEval   = "eval"

	KeywordProveAlgo = "prove_algo"
	KeywordBy        = "by"

	KeywordImplication = "implication"

	KeywordPrint = "print"

	KeywordDoNothing = "do_nothing"

	KeywordCase = "case"

	KeywordProveCaseByCase = "prove_case_by_case"
	KeywordExit            = "exit"
	KeywordHelp            = "help"

	// cart(R,R), (1,2) 表示集合叉乘和集合的元素; set_dim, dim表示集合叉乘和集合的元素的维度； proj, [] 表示集合叉乘的投影和集合的元素的投影; is_cart, is_tuple 表示是集合叉乘和集合的元素的特征
	KeywordCart  = "cart"
	KeywordTuple = "()"

	KeywordIsCart  = "is_cart"
	KeywordIsTuple = "is_tuple"

	KeywordSetDim = "set_dim"
	KeywordDim    = "dim"

	KeywordProj     = "proj"
	KeywordIndexOpt = "[]"

	KeywordHaveCartWithDim = "have_cart_with_dim"

	// 用于一位一位的比较两个tuple。比如 equal_tuple(x, y, 2) 表示 x[1] = y[1] 且 x[2] = y[2]
	KeywordEqualTuple = "equal_tuple"

	KeywordEnumSet        = "{}"
	KeywordIntensionalSet = "{:}"

	KeywordSubsetOf = "subset_of"

	KeywordProveFor = "prove_for"
)

var BuiltinKeywordsSet map[string]struct{} = map[string]struct{}{
	KeywordSet:    {},
	KeywordForall: {},
	KeywordDom:    {},
	// KeywordThen:                 {},
	// KeywordObj:                  {},
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
	KeywordAs:           {},
	KeywordCount:        {},
	KeywordFiniteSet:    {},
	KeywordProveByEnum:  {},
	KeywordItemExistsIn: {},
	KeywordFnTemplate:   {},
	KeywordNPos:         {},
	KeywordLet:          {},
	KeywordClear:        {},
	KeywordTuple:        {},
	KeywordIndexOpt:     {},
	KeywordDoNothing:    {},
	// KeywordExistSetByAxiomOfReplacement:   {},

	KeywordProveIsTransitiveProp: {},

	KeywordProveByInduction: {},

	KeywordLift:        {},
	KeywordNonEmptySet: {},

	KeywordAlgo:   {},
	KeywordReturn: {},
	KeywordIf:     {},
	KeywordEval:   {},

	KeywordProveAlgo: {},
	KeywordBy:        {},

	KeywordImplication: {},

	KeywordPrint: {},

	KeywordCase: {},

	KeywordProveCaseByCase: {},
	KeywordExit:            {},
	KeywordHelp:            {},

	KeywordCart:   {},
	KeywordIsCart: {},
	KeywordSetDim: {},
	KeywordProj:   {},

	KeywordDim: {},

	KeywordHaveCartWithDim: {},

	KeywordEqualTuple:     {},
	KeywordEnumSet:        {},
	KeywordIntensionalSet: {},

	KeywordSubsetOf: {},

	KeywordProveFor: {},
}

const (
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
	KeySymbolDot        = "."
	// PkgNameAtomSeparator is the separator between package name and atom name.
	// For example, in "a.b", "a" is the package name and "b" is the atom name.
	KeySymbolNotEqual     = "!=" // 在parse就立刻变成 not =，exec里没有对它的处理
	KeySymbolDoubleQuote  = "\""
	KeySymbolHash         = "#"
	KeySymbolLargerEqual  = ">="
	KeySymbolLessEqual    = "<="
	KeySymbolPercent      = "%" // prove: 2 % 2 = 0 的时候打印有问题，不知道为什么
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
var SymbolSet map[string]struct{} = map[string]struct{}{
	KeySymbolLargerEqual: {}, // ">="
	KeySymbolLessEqual:   {}, // "<="
	KeySymbolNotEqual:    {}, // "!="
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

var BuiltinObjOrPropNames map[string]struct{} = map[string]struct{}{
	// KeywordObj:           {},
	KeywordSet:           {},
	KeywordNatural:       {},
	KeywordInteger:       {},
	KeywordRational:      {},
	KeywordReal:          {},
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
	KeySymbolPercent:      {}, // prove: 2 % 2 = 0 的时候打印有问题，不知道为什么
	KeySymbolLeftBracket:  {},
	KeySymbolRightBracket: {},
	KeywordFiniteSet:      {},
	// KeywordItemExistsIn:   {},
	// TupleFcFnHead:                         {},
	KeywordCount:       {},
	KeywordNPos:        {},
	KeywordNonEmptySet: {},
	KeywordEval:        {},

	KeywordCart:  {},
	KeywordTuple: {},

	// KeywordIsCart:  {},
	// KeywordIsTuple: {},

	KeywordSetDim: {},
	// KeywordDim:    {},

	// KeywordProj:     {},
	KeywordIndexOpt: {},
}

func IsBuiltinObjOrPropName(name string) bool {
	_, ok := BuiltinObjOrPropNames[name]
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

// KeywordHelpMap stores help messages for each keyword
var KeywordHelpMap = map[string]string{
	KeywordSet:    "",
	KeywordForall: "",
	KeywordDom:    "",
	// KeywordObj:                    "",
	KeywordHave:                   "",
	KeywordFn:                     "",
	KeywordProp:                   "",
	KeywordKnow:                   "",
	KeywordExist:                  "",
	KeywordSt:                     "",
	KeywordExistProp:              "",
	KeywordClaim:                  "",
	KeywordProve:                  "",
	KeywordImport:                 "",
	KeywordNot:                    "",
	KeywordProveByContradiction:   "",
	KeywordProveInEachCase:        "",
	KeywordOr:                     "",
	KeywordProveIsCommutativeProp: "",
	KeywordNatural:                "",
	KeywordInteger:                "",
	KeywordRational:               "",
	KeywordReal:                   "",
	KeywordIn:                     "",
	KeywordAs:                     "",
	KeywordCount:                  "",
	KeywordFiniteSet:              "",
	KeywordProveByEnum:            "",
	KeywordItemExistsIn:           "",
	KeywordFnTemplate:             "",
	KeywordNPos:                   "",
	KeywordLet:                    "",
	KeywordClear:                  "",
	KeywordProveByInduction:       "",
	KeywordLift:                   "",
	KeywordNonEmptySet:            "",
	KeywordProveIsTransitiveProp:  "",
	KeywordProveInRangeSet:        "",
	KeywordProveInRange:           "",
	KeywordAlgo:                   "",
	KeywordReturn:                 "",
	KeywordIf:                     "",
	KeywordEval:                   "",
	KeywordProveAlgo:              "",
	KeywordBy:                     "",
	KeywordImplication:            "",
	KeywordPrint:                  "",
	KeywordCase:                   "",
	KeywordProveCaseByCase:        "",
	KeywordExit:                   "exit current REPL session",
	KeywordHelp:                   "show this help message",
}

const PkgNameAtomSeparator = KeySymbolDot
