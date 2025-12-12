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
	KeywordIn = "in"

	KeywordSet         = "set"
	KeywordNonEmptySet = "nonempty_set"
	KeywordFiniteSet   = "finite_set"

	KeywordIsASet         = "is_a_set"
	KeywordIsAFiniteSet   = "is_a_finite_set"
	KeywordIsANonEmptySet = "is_a_nonempty_set"

	KeywordNot    = "not"
	KeywordOr     = "or"
	KeywordForall = "forall"
	KeywordExist  = "exist"

	KeywordProp      = "prop"
	KeywordExistProp = "exist_prop"

	KeywordHave = "have"
	KeywordLet  = "let"

	KeywordNPos     = "N_pos"
	KeywordNatural  = "N"
	KeywordInteger  = "Z"
	KeywordRational = "Q"
	KeywordReal     = "R"
	KeywordFn       = "fn"

	KeywordCart   = "cart"
	KeywordIsCart = "is_cart"
	KeywordSetDim = "set_dim"
	KeywordProj   = "proj"

	KeywordTuple    = "()"
	KeywordDim      = "dim"
	KeywordIsTuple  = "is_tuple"
	KeywordIndexOpt = "[]"

	KeywordListSet    = "{}"
	KeywordSetBuilder = "{:}"
	KeywordCount      = "count"

	KeywordKnow      = "know"
	KeywordDoNothing = "do_nothing"

	KeywordProveByContradiction = "prove_by_contradiction"
	KeywordProveInEachCase      = "prove_in_each_case"
	KeywordProveByEnum          = "prove_by_enum"
	KeywordProveByInduction     = "prove_by_induction"
	KeywordProveInRangeSet      = "prove_in_range_set"
	KeywordProveInRange         = "prove_in_range"
	KeywordProveCaseByCase      = "prove_case_by_case"

	KeywordFnTemplate = "fn_template"

	KeywordClaim = "claim"
	KeywordProve = "prove"
	KeywordDom   = "dom"
	KeywordCase  = "case"
	KeywordSt    = "st"

	KeywordProveIsCommutativeProp = "prove_is_commutative_prop" // 这个 keyword是真的在工作的
	KeywordProveIsTransitiveProp  = "prove_is_transitive_prop"

	KeywordImport = "import"
	KeywordClear  = "clear"
	KeywordPrint  = "print"
	KeywordExit   = "exit"
	KeywordHelp   = "help"
	KeywordAs     = "as"

	KeywordProveAlgo = "prove_algo"
	KeywordAlgo      = "algo"
	KeywordReturn    = "return"
	KeywordIf        = "if"
	KeywordBy        = "by"
	KeywordEval      = "eval"

	KeywordEqualTuple = "equal_tuple"
	KeywordEqualSet   = "equal_set"
	KeywordSubsetOf   = "subset_of"

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
	KeywordCount:       {},
	KeywordFiniteSet:   {},
	KeywordProveByEnum: {},
	// KeywordItemExistsIn: {},
	KeywordFnTemplate: {},
	KeywordNPos:       {},
	KeywordLet:        {},
	KeywordClear:      {},
	KeywordTuple:      {},
	KeywordIndexOpt:   {},
	KeywordDoNothing:  {},
	// KeywordExistSetByAxiomOfReplacement:   {},

	KeywordProveIsTransitiveProp: {},

	KeywordProveByInduction: {},

	KeywordNonEmptySet: {},

	KeywordAlgo:   {},
	KeywordReturn: {},
	KeywordIf:     {},
	KeywordEval:   {},

	KeywordProveAlgo: {},
	KeywordBy:        {},

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

	KeywordEqualTuple: {},
	KeywordListSet:    {},
	KeywordSetBuilder: {},

	KeywordSubsetOf: {},

	KeywordProveFor: {},

	KeywordEqualSet: {},

	KeywordAs: {},

	KeywordIsASet:         {},
	KeywordIsAFiniteSet:   {},
	KeywordIsANonEmptySet: {},
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
	// KeywordSet:           {},
	KeywordNatural:       {},
	KeywordInteger:       {},
	KeywordRational:      {},
	KeywordReal:          {},
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
	// KeywordFiniteSet:      {},
	// KeywordItemExistsIn:   {},
	KeywordCount: {},
	KeywordNPos:  {},
	KeywordEval:  {},

	KeywordCart:  {},
	KeywordTuple: {},

	// KeywordIsCart:  {},
	// KeywordIsTuple: {},

	KeywordSetDim: {},
	// KeywordDim:    {},

	// KeywordProj:     {},
	KeywordIndexOpt: {},

	KeywordIsASet:         {},
	KeywordIsAFiniteSet:   {},
	KeywordIsANonEmptySet: {},
}

func IsBuiltinObjOrPropName(name string) bool {
	_, ok := BuiltinObjOrPropNames[name]
	return ok
}

func IsBuiltinAtom(name string) bool {
	_, ok := BuiltinAtomNames[name]
	return ok
}

func IsBuiltinKeywordOrBuiltinSymbolOrNumber(name string) bool {
	if IsKeyword(name) || IsKeySymbol(name) || (name[0] >= '0' && name[0] <= '9') {
		return true
	}
	return false
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
	KeywordCount:                  "",
	KeywordFiniteSet:              "",
	KeywordProveByEnum:            "",

	// KeywordItemExistsIn:           "",

	KeywordFnTemplate:            "",
	KeywordNPos:                  "",
	KeywordLet:                   "",
	KeywordClear:                 "",
	KeywordProveByInduction:      "",
	KeywordNonEmptySet:           "",
	KeywordProveIsTransitiveProp: "",
	KeywordProveInRangeSet:       "",
	KeywordProveInRange:          "",
	KeywordAlgo:                  "",
	KeywordReturn:                "",
	KeywordIf:                    "",
	KeywordEval:                  "",
	KeywordProveAlgo:             "",
	KeywordBy:                    "",
	KeywordPrint:                 "",
	KeywordCase:                  "",
	KeywordProveCaseByCase:       "",
	KeywordExit:                  "exit current REPL session",
	KeywordHelp:                  "show this help message",
}

const PkgNameAtomSeparator = KeySymbolDot

func IsNPosOrNOrZOrQOrR(name string) bool {
	return name == KeywordNPos || name == KeywordNatural || name == KeywordInteger || name == KeywordRational || name == KeywordReal
}

var BuiltinAtomNames map[string]struct{} = map[string]struct{}{
	KeywordNatural:    {},
	KeywordInteger:    {},
	KeywordRational:   {},
	KeywordReal:       {},
	KeywordCount:      {},
	KeywordNPos:       {},
	KeywordCart:       {},
	KeywordTuple:      {},
	KeywordSetDim:     {},
	KeywordDim:        {},
	KeywordProj:       {},
	KeywordIndexOpt:   {},
	KeywordListSet:    {},
	KeywordSetBuilder: {},
	KeySymbolPlus:     {},
	KeySymbolMinus:    {},
	KeySymbolStar:     {},
	KeySymbolPower:    {},
	KeywordFn:         {},
}
