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
	KeywordSet    = "set"
	KeywordForall = "forall"
	// KeywordWhen      = "when"
	KeywordDom       = "dom" // 必须存在，因为有时候只有要求没then
	KeywordThen      = "then"
	KeywordObj       = "obj"
	KeywordExistObj  = "exist_obj"
	KeywordFn        = "fn"
	KeywordProp      = "prop"
	KeywordKnow      = "know"
	KeywordExist     = "exist"
	KeywordSt        = "st"
	KeywordExistProp = "exist_prop"
	// KeywordConstructorProp      = "constructor_prop"
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

	KeywordAnd = "and"
	KeywordOr  = "or"

	// Syntax and Semantics Sugar
	KeywordCommutative = "commutative"
	KeywordAssociative = "associative"

	// Builtin Types
	KeywordNatural  = "nat"  // e.g. 0
	KeywordInt      = "int"  // e.g. -1
	KeywordRational = "rat"  // e.g. -1.1
	KeywordReal     = "real" // e.g. pi

	// Builtin Functions
	KeywordIs   = "is"
	KeywordIn   = "in"
	KeyWordFrac = "frac"

	KeywordExtend = "extend"
)

var keywordsSet map[string]struct{} = map[string]struct{}{
	// 常规关键字
	KeywordSet:    {},
	KeywordForall: {},
	// KeywordWhen:      {},
	KeywordDom:       {},
	KeywordThen:      {},
	KeywordObj:       {},
	KeywordExistObj:  {},
	KeywordFn:        {},
	KeywordProp:      {},
	KeywordKnow:      {},
	KeywordExistProp: {},
	KeywordSt:        {},
	// KeywordConstructorProp:      {},
	KeywordClaim:                {},
	KeywordProve:                {},
	KeywordPub:                  {},
	KeywordImport:               {},
	KeywordPackage:              {},
	KeywordNot:                  {},
	KeywordImpl:                 {},
	KeywordAs:                   {},
	KeywordAxiom:                {},
	KeywordProveByContradiction: {},
	KeywordThm:                  {},
	KeywordIff:                  {},
	KeywordExist:                {},

	// 语法糖
	KeywordCommutative: {},
	KeywordAssociative: {},

	KeywordAnd: {},
	KeywordOr:  {},

	// 内置类型
	KeywordNatural:  {},
	KeywordInt:      {},
	KeywordRational: {},
	KeywordReal:     {},

	// 内置函数
	KeywordIs: {},
	KeywordIn: {},

	KeywordExtend: {},
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
