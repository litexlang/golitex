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
// Litex discord server: https://discord.gg/uvrHM7eS

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
	KeywordPub                  = "pub"
	KeywordImport               = "import"
	KeywordPackage              = "package"
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
	KeywordIs                   = "is"
	KeywordIn                   = "in"
	KeywordProveByMathInduction = "prove_by_math_induction"
	KeywordAs                   = "as"
	KeywordProveOr              = "prove_or"
	KeywordSuppose              = "suppose"
	KeywordWith                 = "with"
	// 用户用不到的keyword，但litex内部会用
	// litex version 0.2 的时候可以考虑实现。这样的话fn所在的集合也能像obj一样简单了
	// KeywordFnSet = "fn_set"
	// litex version 0.3 的时候可以考虑实现。这样的话set所在的集合也能像obj一样简单了
	// KeywordSetSet = "set_set"
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
	KeywordPub:                  {},
	KeywordImport:               {},
	KeywordPackage:              {},
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
	KeywordIs:                   {},
	KeywordIn:                   {},
	KeywordProveByMathInduction: {},
	KeywordAs:                   {},
	KeywordProveOr:              {},
	KeywordSuppose:              {},
	KeywordWith:                 {},
	KeywordComplex:              {},
	KeywordImaginary:            {},
}

const (
	// Builtin Symbols
	KeySymbolColon                  = ":"
	KeySymbolLeftBrace              = "("
	KeySymbolRightBrace             = ")"
	KeySymbolComma                  = ","
	KeySymbolDollar                 = "$"
	KeySymbolEqual                  = "="
	KeySymbolSlash                  = "/"
	KeySymbolPlus                   = "+"
	KeySymbolMinus                  = "-"
	KeySymbolStar                   = "*"
	KeySymbolPower                  = "^"
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
	KeySymbolNotEqual               = "!=" // 在parse就立刻变成 not =，exec里没有对它的处理
	KeySymbolQuestion               = "?"
	KeySymbolStarStar               = "**"
	KeySymbolDoubleQuote            = "\""
	KeySymbolSingleQuote            = "'"
	KeySymbolBacktick               = "`"
	KeySymbolEqualGreaterEqual      = "=>"
	KeySymbolMinusGreaterRightArrow = "->"
	KeySymbolSemicolon              = ";"
	KeySymbolHash                   = "#"
	KeySymbolAt                     = "@"
	KeySymbolLargerEqual            = ">="
	KeySymbolLessEqual              = "<="
	KeySymbolEquivalent             = "<=>"
	// It's possible for me to overload the meaning of "=" to mean "set equal", but I don't want to do that(I do not want to overload the meaning of "=" too much, which can be very tiring for future maintainers and make confusions), so I use a new keyword
	KeySymbolEqualEqual      = "=="  // check fn equal. TODO: 要调整语义
	KeySymbolEqualEqualEqual = "===" // check set equal. TODO: 要调整语义
	KeySymbolGreaterGreater  = ">>"
	KeySymbolLessLess        = "<<"
	KeySymbolPercent         = "%" // prove: 2 % 2 = 0 的时候打印有问题，不知道为什么
)

var symbolSet map[string]struct{} = map[string]struct{}{
	// 双字符符号（长度 2）
	KeySymbolAndAnd:                 {}, // "&&"
	KeySymbolEqualEqual:             {}, // "=="
	KeySymbolEqualGreaterEqual:      {}, // "=>"
	KeySymbolLargerEqual:            {}, // ">="
	KeySymbolLessEqual:              {}, // "<="
	KeySymbolMinusGreaterRightArrow: {}, // "->"
	KeySymbolNotEqual:               {}, // "!="
	KeySymbolPipePipe:               {}, // "||"
	KeySymbolPlusPlus:               {}, // "++"
	KeySymbolMinusMinus:             {}, // "--"
	KeySymbolStarStar:               {}, // "**"
	KeySymbolColonColon:             {}, // "::"

	// 单字符符号（长度 1）
	KeySymbolAt:          {}, // "@"
	KeySymbolBackslash:   {}, // "\\"
	KeySymbolBacktick:    {}, // "`"
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
	KeySymbolPipe:      {}, // "|"
	KeySymbolPlus:      {}, // "+"
	KeySymbolQuestion:  {}, // "?"
	// KeySymbolRightBracket: {}, // "]"
	// KeySymbolRightCurly:      {}, // "}"
	KeySymbolRightBrace:      {}, // ")"
	KeySymbolSemicolon:       {}, // ";"
	KeySymbolSingleQuote:     {}, // "'"
	KeySymbolSlash:           {}, // "/"
	KeySymbolStar:            {}, // "*"
	KeySymbolTilde:           {}, // "~"
	KeySymbolAnd:             {}, // "&"
	KeySymbolEquivalent:      {}, // "<=>"
	KeySymbolEqualEqualEqual: {}, // "==="
	KeySymbolGreaterGreater:  {}, // ">>"
	KeySymbolLessLess:        {}, // "<<"
	KeySymbolPercent:         {}, // "%"
}
