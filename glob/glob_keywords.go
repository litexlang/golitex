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

// ! 每次新增keyword的时候，要记住把它往isKeyword里加
const (
	KeywordSet       = "set"
	KeywordForall    = "forall"
	KeywordDom       = "dom" // 这是一种语法糖。本质上只要在定义集合的时候写了对集合的要求，那dom就不必要的，因为dom本质上是 ”临时添加新的要求"
	KeywordThen      = "then"
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
	KeywordPub       = "pub"
	KeywordImport    = "import"
	KeywordPackage   = "package"
	KeywordNot       = "not"
	// KeywordAs                    = "as"
	KeywordProveByContradiction = "prove_by_contradiction"
	KeywordProveInEachCase      = "prove_in_each_case" // 必要：和or一起使用
	KeywordIff                  = "iff"
	KeywordAnd                  = "and"
	KeywordOr                   = "or"
	KeywordCommutativeProp      = "commutative_prop"
	KeywordCommutativeFn        = "commutative_fn" // must-have: 否则 a+b=b+a不能验证
	KeywordAssociativeFn        = "associative_fn" // must-have: 否则 a+1+1=a+2不能验证
	KeywordNatural              = "nat"            // e.g. 0
	KeywordInt                  = "int"            // e.g. -1
	KeywordRational             = "rat"            // e.g. -1.1
	KeywordReal                 = "real"           // e.g. pi
	KeywordIs                   = "is"
	KeywordIn                   = "in"
	KeywordMathInduction        = "math_induction"
	KeywordFrac                 = "frac"
	KeywordExtend               = "extend"

	// litex version 0.2 的时候可以考虑实现。这样的话fn所在的集合也能像obj一样简单了
	KeywordFnSet = "fn_set"
	// litex version 0.3 的时候可以考虑实现。这样的话set所在的集合也能像obj一样简单了
	KeywordSetSet = "set_set"

	KeywordR = "R" // r as postfix for real number
	KeywordF = "F" // f as postfix for float number
	KeywordI = "i" // i for imaginary part of a complex number
	KeywordN = "N" // n as postfix for natural number
	KeywordC = "C" // c as postfix for complex number
)

var BuiltinKeywordsSet map[string]struct{} = map[string]struct{}{
	KeywordSet:       {},
	KeywordForall:    {},
	KeywordDom:       {},
	KeywordThen:      {},
	KeywordObj:       {},
	KeywordHave:      {},
	KeywordFn:        {},
	KeywordProp:      {},
	KeywordKnow:      {},
	KeywordExistProp: {},
	KeywordSt:        {},
	KeywordClaim:     {},
	KeywordProve:     {},
	KeywordPub:       {},
	KeywordImport:    {},
	KeywordPackage:   {},
	KeywordNot:       {},
	// KeywordAs:                    {},
	KeywordProveByContradiction: {},
	KeywordProveInEachCase:      {},
	KeywordIff:                  {},
	KeywordExist:                {},
	KeywordCommutativeProp:      {},
	KeywordCommutativeFn:        {},
	KeywordAssociativeFn:        {},
	KeywordAnd:                  {},
	KeywordOr:                   {},
	KeywordNatural:              {},
	KeywordInt:                  {},
	KeywordRational:             {},
	KeywordReal:                 {},
	KeywordIs:                   {},
	KeywordIn:                   {},
	KeywordExtend:               {},
	KeywordFnSet:                {},
	KeywordSetSet:               {},
	KeywordMathInduction:        {},

	KeywordR: {},
	KeywordF: {},
	KeywordI: {},
	KeywordN: {},
	KeywordC: {},
}

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
	KeySymbolBackslash              = "\\"
	KeySymbolDot                    = "."
	KeySymbolColonColon             = "::"
	KeySymbolPlusPlus               = "++"
	KeySymbolMinusMinus             = "--"
	KeySymbolAndAnd                 = "&&"
	KeySymbolPipePipe               = "||"
	KeySymbolEqualEqual             = "=="
	KeySymbolNotEqual               = "!="
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

var symbolSet map[string]struct{} = map[string]struct{}{
	// 双字符符号（长度 2）
	KeySymbolAndAnd:                 {}, // "&&"
	KeySymbolEqualEqual:             {}, // "=="
	KeySymbolEqualGreaterRightArrow: {}, // "=>"
	KeySymbolMinusGreaterRightArrow: {}, // "->"
	KeySymbolNotEqual:               {}, // "!="
	KeySymbolPipePipe:               {}, // "||"
	KeySymbolPlusPlus:               {}, // "++"
	KeySymbolMinusMinus:             {}, // "--"
	KeySymbolStarStar:               {}, // "**"
	KeySymbolColonColon:             {}, // "::"

	// 单字符符号（长度 1）
	KeySymbolAt:           {}, // "@"
	KeySymbolBackslash:    {}, // "\\"
	KeySymbolBacktick:     {}, // "`"
	KeySymbolCaret:        {}, // "^"
	KeySymbolColon:        {}, // ":"
	KeySymbolComma:        {}, // ","
	KeySymbolDot:          {}, // "."
	KeySymbolDollar:       {}, // "$"
	KeySymbolDoubleQuote:  {}, // "\""
	KeySymbolEqual:        {}, // "="
	KeySymbolExclaim:      {}, // "!"
	KeySymbolGreater:      {}, // ">"
	KeySymbolHash:         {}, // "#"
	KeySymbolLeftBracket:  {}, // "["
	KeySymbolLeftCurly:    {}, // "{"
	KeySymbolLeftBrace:    {}, // "("
	KeySymbolLess:         {}, // "<"
	KeySymbolMinus:        {}, // "-"
	KeySymbolPipe:         {}, // "|"
	KeySymbolPlus:         {}, // "+"
	KeySymbolQuestion:     {}, // "?"
	KeySymbolRightBracket: {}, // "]"
	KeySymbolRightCurly:   {}, // "}"
	KeySymbolRightBrace:   {}, // ")"
	KeySymbolSemicolon:    {}, // ";"
	KeySymbolSingleQuote:  {}, // "'"
	KeySymbolSlash:        {}, // "/"
	KeySymbolStar:         {}, // "*"
	KeySymbolTilde:        {}, // "~"
	KeySymbolAnd:          {}, // "&"
	KeySymbolLargerEqual:  {}, // ">="
	KeySymbolLessEqual:    {}, // "<="
}
