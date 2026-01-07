// Copyright Jiachen Shen.
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

	KeywordIsASet         = "is_set"
	KeywordIsAFiniteSet   = "is_finite_set"
	KeywordIsANonEmptySet = "is_nonempty_set"

	KeywordNot    = "not"
	KeywordOr     = "or"
	KeywordForall = "forall"
	KeywordExist  = "exist"

	KeywordProp = "prop"

	// KeywordExistProp = "exist_prop"

	KeywordImply      = "imply"
	KeywordProveImply = "prove_infer"

	KeywordHave = "have"
	KeywordLet  = "let"

	KeywordNPos     = "N_pos"
	KeywordNatural  = "N"
	KeywordInteger  = "Z"
	KeywordRational = "Q"
	KeywordReal     = "R"

	KeywordCart   = "cart"
	KeywordIsCart = "is_cart"
	KeywordSetDim = "set_dim"
	KeywordProj   = "proj"

	KeywordTuple         = "tuple"
	KeywordDim           = "dim"
	KeywordIsTuple       = "is_tuple"
	KeywordObjAtIndexOpt = "obj_at_index"

	KeywordListSet     = "list_set"
	KeywordSetBuilder  = "set_builder"
	KeywordCount       = "count"
	KeywordRange       = "range"
	KeywordClosedRange = "closed_range"

	KeywordKnow      = "know"
	KeywordDoNothing = "do_nothing"

	KeywordProveByContradiction = "prove_by_contradiction"
	KeywordProveByEnum          = "prove_by_enum"
	KeywordProveByInduction     = "prove_by_induction"
	KeywordProveCaseByCase      = "prove_case_by_case"
	KeywordProveFor             = "prove_for"

	KeywordFn    = "fn"
	KeywordFnSet = "fn_set"

	KeywordClaim = "claim"
	KeywordProve = "prove"

	KeywordDom  = "dom"
	KeywordCase = "case"
	KeywordSt   = "st"
	KeywordAs   = "as"

	KeywordProveIsCommutativeProp = "prove_is_commutative_prop"
	KeywordProveIsTransitiveProp  = "prove_is_transitive_prop"

	KeywordImport = "import"
	KeywordClear  = "clear"
	KeywordExit   = "exit"
	KeywordRun    = "run"

	KeywordProveAlgo = "prove_algo"
	KeywordAlgo      = "algo"
	KeywordReturn    = "return"
	KeywordIf        = "if"
	KeywordBy        = "by"
	KeywordEval      = "eval"
	KeywordVal       = "val"

	KeywordEqualSet    = "equal_set"
	KeywordNotEqualSet = "not_equal_set"
	KeywordSubsetOf    = "subset_of"
	KeywordSupersetOf  = "superset_of"
	KeywordEqualTuple  = "equal_tuple"

	KeywordCup       = "cup"
	KeywordCap       = "cap"
	KeywordUnion     = "union"
	KeywordIntersect = "intersect"
	KeywordPowerSet  = "power_set"
	KeywordSetMinus  = "set_minus"
	KeywordSetDiff   = "set_diff"
	KeywordChoice    = "choice"

	KeywordProveExist = "prove_exist"

	KeywordRPos = "R_pos"
	KeywordRNeg = "R_neg"
	KeywordZNeg = "Z_neg"
	KeywordQNeg = "Q_neg"
	KeywordQPos = "Q_pos"
)

var BuiltinKeywordsSet map[string]struct{} = map[string]struct{}{
	KeywordSet:        {},
	KeywordForall:     {},
	KeywordDom:        {},
	KeywordImply:      {},
	KeywordProveImply: {},
	KeywordHave:       {},
	KeywordFn:         {},
	KeywordProp:       {},
	KeywordKnow:       {},
	// KeywordExistProp:            {},
	KeywordSt:                   {},
	KeywordClaim:                {},
	KeywordProve:                {},
	KeywordImport:               {},
	KeywordNot:                  {},
	KeywordProveByContradiction: {},
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
	KeywordFnSet:         {},
	KeywordNPos:          {},
	KeywordLet:           {},
	KeywordClear:         {},
	KeywordTuple:         {},
	KeywordObjAtIndexOpt: {},
	KeywordDoNothing:     {},
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

	KeywordCase: {},

	KeywordProveCaseByCase: {},
	KeywordExit:            {},

	KeywordCart:   {},
	KeywordIsCart: {},
	KeywordSetDim: {},
	KeywordProj:   {},

	KeywordDim: {},

	KeywordListSet:    {},
	KeywordSetBuilder: {},

	KeywordSubsetOf:   {},
	KeywordSupersetOf: {},
	KeywordProveFor:   {},

	KeywordEqualSet: {},

	KeywordEqualTuple: {},

	KeywordAs: {},

	KeywordIsASet:         {},
	KeywordIsAFiniteSet:   {},
	KeywordIsANonEmptySet: {},

	KeywordRange: {},

	// KeywordIsNonEmptyWithItem: {},

	KeywordRun: {},

	KeywordUnion:     {},
	KeywordIntersect: {},
	KeywordPowerSet:  {},
	KeywordCup:       {},
	KeywordCap:       {},
	KeywordSetMinus:  {},
	KeywordSetDiff:   {},

	KeywordProveExist: {},

	KeywordRPos: {},
	KeywordRNeg: {},
	KeywordZNeg: {},
	KeywordQNeg: {},
	KeywordQPos: {},
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
	// KeySymbolAt         = "@"
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
	KeySymbolRightArrow:   {}, // "=>"
	KeySymbolSemiColon:    {}, // ";"
	KeySymbolEquivalent:   {}, // "<=>"
	KeySymbolBackSlash:    {},
	// KeySymbolQuestionMark: {}, // "?"
}

var BuiltinAtomNames map[string]struct{} = map[string]struct{}{
	KeywordNatural:       {},
	KeywordInteger:       {},
	KeywordRational:      {},
	KeywordReal:          {},
	KeywordCount:         {},
	KeywordNPos:          {},
	KeywordCart:          {},
	KeywordTuple:         {},
	KeywordSetDim:        {},
	KeywordDim:           {},
	KeywordProj:          {},
	KeywordObjAtIndexOpt: {},
	KeywordListSet:       {},
	KeywordSetBuilder:    {},
	KeySymbolPlus:        {},
	KeySymbolMinus:       {},
	KeySymbolStar:        {},
	KeySymbolPower:       {},
	KeySymbolSlash:       {},
	KeySymbolPercent:     {},

	KeywordUnion:     {},
	KeywordIntersect: {},
	KeywordPowerSet:  {},
	KeywordCup:       {},
	KeywordCap:       {},
	KeywordSetMinus:  {},
	KeywordSetDiff:   {},

	KeywordRPos: {},
	KeywordRNeg: {},
	KeywordZNeg: {},
	KeywordQNeg: {},
	KeywordQPos: {},

	KeywordVal:    {},
	KeywordChoice: {},
}

var BuiltinPropNames map[string]struct{} = map[string]struct{}{
	KeywordIn:             {},
	KeywordIsASet:         {},
	KeywordIsAFiniteSet:   {},
	KeywordIsANonEmptySet: {},
	KeywordIsCart:         {},
	KeywordIsTuple:        {},
	KeywordEqualSet:       {},
	KeywordNotEqualSet:    {},
	KeywordSubsetOf:       {},
	KeySymbolEqual:        {},
	KeySymbolNotEqual:     {},
	KeySymbolLargerEqual:  {},
	KeySymbolLessEqual:    {},
	KeySymbolGreater:      {},
	KeySymbolLess:         {},
	KeywordEqualTuple:     {},
}

func IsBuiltinPropName(name string) bool {
	_, ok := BuiltinPropNames[name]
	return ok
}

func IsBuiltinName(name string) bool {
	_, ok := BuiltinKeywordsThatCanNotBeUsedAsName[name]
	return ok
}

func IsBuiltinAtomName(name string) bool {
	_, ok := BuiltinAtomNames[name]
	return ok
}

var BuiltinKeywordsThatCanNotBeUsedAsName map[string]struct{} = map[string]struct{}{
	KeywordSet:        {},
	KeywordForall:     {},
	KeywordDom:        {},
	KeywordImply:      {},
	KeywordProveImply: {},
	KeywordHave:       {},
	KeywordFn:         {},
	KeywordProp:       {},
	KeywordKnow:       {},
	// KeywordExistProp:              {},
	KeywordSt:                     {},
	KeywordClaim:                  {},
	KeywordProve:                  {},
	KeywordImport:                 {},
	KeywordNot:                    {},
	KeywordProveByContradiction:   {},
	KeywordExist:                  {},
	KeywordProveIsCommutativeProp: {},
	KeywordOr:                     {},
	KeywordNatural:                {},
	KeywordInteger:                {},
	KeywordRational:               {},
	KeywordReal:                   {},
	KeywordIn:                     {},
	KeywordCount:                  {},
	KeywordFiniteSet:              {},
	KeywordProveByEnum:            {},
	KeywordFnSet:                  {},
	KeywordNPos:                   {},
	KeywordLet:                    {},
	KeywordClear:                  {},
	KeywordTuple:                  {},
	KeywordObjAtIndexOpt:          {},
	KeywordDoNothing:              {},
	KeywordProveIsTransitiveProp:  {},
	KeywordProveByInduction:       {},
	KeywordNonEmptySet:            {},
	KeywordAlgo:                   {},
	KeywordReturn:                 {},
	KeywordIf:                     {},
	KeywordEval:                   {},
	KeywordProveAlgo:              {},
	KeywordBy:                     {},
	KeywordCase:                   {},
	KeywordProveCaseByCase:        {},
	KeywordExit:                   {},
	KeywordCart:                   {},
	KeywordSetDim:                 {},
	KeywordListSet:                {},
	KeywordSetBuilder:             {},
	KeywordProveFor:               {},
	KeywordAs:                     {},
	KeywordIsASet:                 {},
	KeywordIsAFiniteSet:           {},
	KeywordIsANonEmptySet:         {},
	// KeywordIsNonEmptyWithItem:     {},
	KeywordRun:       {},
	KeywordUnion:     {},
	KeywordIntersect: {},
	KeywordRPos:      {},
	KeywordRNeg:      {},
	KeywordZNeg:      {},
	KeywordQNeg:      {},
	KeywordQPos:      {},
	KeywordPowerSet:  {},
	KeywordCup:       {},
	KeywordCap:       {},
	KeywordSetMinus:  {},
	KeywordSetDiff:   {},
	KeywordVal:       {},
}
