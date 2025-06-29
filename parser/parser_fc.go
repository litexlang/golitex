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

package litex_parser

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
	"strings"
)

func (tb *tokenBlock) RawFc() (ast.Fc, error) {
	expr, err := tb.fcInfixExpr(glob.PrecLowest)
	if err != nil {
		return nil, err
	}

	if _, ok := expr.(*ast.FcAtom); ok {
		return expr, fmt.Errorf("invalid first citizen: %s", expr)
	}

	return expr, nil
}

func (tb *tokenBlock) squareBracketExpr() (ast.Fc, error) {
	fc, err := tb.fcAtomAndFcFn()
	if err != nil {
		return nil, err
	}

	if !tb.header.is(glob.KeySymbolLeftBracket) {
		return fc, nil
	}

	tb.header.skip(glob.KeySymbolLeftBracket)

	isAtIndexOp := true

	if tb.header.is(glob.KeySymbolLeftBracket) {
		tb.header.skip(glob.KeySymbolLeftBracket)
		isAtIndexOp = false
	}

	if tb.header.ExceedEnd() {
		return nil, fmt.Errorf("unexpected end of input after '['")
	}

	fcInBracket, err := tb.RawFc()
	if err != nil {
		return nil, err
	}

	if tb.header.ExceedEnd() {
		return nil, fmt.Errorf("unexpected end of input after ']'")
	}

	if isAtIndexOp {
		if err := tb.header.skip(glob.KeySymbolRightBracket); err != nil {
			return nil, fmt.Errorf("expected '%s': %v", glob.KeySymbolRightBracket, err)
		}

		return ast.NewFcFn(ast.FcAtom(glob.AtIndexOp), []ast.Fc{fc, fcInBracket}), nil
	} else {
		if err := tb.header.skip(glob.KeySymbolRightBracket); err != nil {
			return nil, fmt.Errorf("expected '%s': %v", glob.KeySymbolRightBracket, err)
		}

		if err := tb.header.skip(glob.KeySymbolRightBracket); err != nil {
			return nil, fmt.Errorf("expected '%s': %v", glob.KeySymbolRightBracket, err)
		}

		return ast.NewFcFn(ast.FcAtom(glob.GetIndexOfOp), []ast.Fc{fc, fcInBracket}), nil
	}
}

// “数学”优先级越高，越是底层。所以把括号表达式放在这里处理
func (tb *tokenBlock) fcAtomAndFcFn() (ast.Fc, error) {
	var expr ast.Fc
	var err error

	if tb.header.is(glob.KeywordFn) {
		return tb.fnSet()
	} else if tb.header.is(glob.KeySymbolLeftBrace) {
		expr, err = tb.bracedExpr()
		if err != nil {
			return nil, err
		}
		return tb.consumeBracedFc(expr)
	} else if tb.header.curTokenBeginWithNumber() {
		expr, err = tb.numberStr()
		if err != nil {
			return nil, err
		}
		if tb.header.is(glob.KeySymbolLeftBrace) {
			return nil, fmt.Errorf("unexpected left brace after number")
		} else {
			return expr, nil
		}
	} else {
		fcStr, err := tb.rawFcAtom()
		if err != nil {
			return nil, tbErr(err, tb)
		}
		ret, err := tb.consumeBracedFc(fcStr)
		if err != nil {
			return nil, tbErr(err, tb)
		}
		// dot
		if tb.header.is(glob.MemberAccessOpt) {
			tb.header.skip(glob.MemberAccessOpt)
			dotFc, err := tb.rawFcAtom()
			if err != nil {
				return nil, tbErr(err, tb)
			}
			ret = ast.NewFcFn(ast.FcAtom(glob.MemberAccessOpt), []ast.Fc{ret, dotFc})
		}
		return ret, nil
	}
}

func (tb *tokenBlock) rawFcAtom() (ast.FcAtom, error) {
	values := []string{}

	value, err := tb.header.next()
	if err != nil {
		return ast.EmptyFcAtom, err
	}

	for tb.header.is(glob.KeySymbolColonColon) {
		tb.header.skip(glob.KeySymbolColonColon)
		values = append(values, value)
		value, err = tb.header.next()
		if err != nil {
			return ast.EmptyFcAtom, err
		}
	}

	// if glob.IsBuiltinKeywordKeySymbol_NeverBeFcAtom(value) {
	// return ast.NewFcAtom(glob.BuiltinPkgName, value), fmt.Errorf("invalid first citizen: %s", value)
	// 	return ast.NewFcAtom(value), fmt.Errorf("invalid first citizen: %s", value)
	// } else {
	// 不是内置元素，不是数字
	if glob.CurrentPkg != "" && !glob.IsBuiltinKeywordOrBuiltinSymbolOrNumber(value) {
		values = append([]string{glob.CurrentPkg}, values...)
	}

	values = append(values, value)

	// return ast.NewFcAtom(strings.Join(pkgNames, glob.KeySymbolColonColon), value), nil
	return ast.FcAtom(strings.Join(values, glob.KeySymbolColonColon)), nil

	// }
}

func (tb *tokenBlock) fcInfixExpr(currentPrec glob.BuiltinOptPrecedence) (ast.Fc, error) {
	left, err := tb.unaryOptFc()
	if err != nil {
		return nil, err
	}

	for !tb.header.ExceedEnd() {
		curToken, err := tb.header.currentToken()
		if err != nil {
			return nil, fmt.Errorf("unexpected end of input while parsing infix expression")
		}

		if curToken == glob.RelaFnPrefix {
			tb.header.skip("") // 消耗curToken

			fn, err := tb.RawFc()
			if err != nil {
				return nil, err
			}

			right, err := tb.fcInfixExpr(glob.PrecLowest)
			if err != nil {
				return nil, err
			}

			left = ast.NewFcFn(fn, []ast.Fc{left, right})
			break
		}

		// 检查是否是运算符
		curPrec, isBinary := glob.BuiltinOptPrecedenceMap[curToken]

		if !isBinary {
			break
		}

		if curPrec <= currentPrec {
			break
		}

		tb.header.skip("") // 消耗运算符
		right, err := tb.fcInfixExpr(curPrec)
		if err != nil {
			return nil, err
		}

		leftHead := ast.FcAtom(curToken)
		left = ast.NewFcFn(
			leftHead,
			[]ast.Fc{left, right},
		)
	}

	return left, nil
}

// func (tb *tokenBlock) fcPrimaryExpr() (ast.Fc, error) {
// 	if tb.ExceedEnd() {
// 		return nil, fmt.Errorf("unexpected end of input, expected expression")
// 	}

// 	return tb.unaryOptFc()
// }

func (tb *tokenBlock) unaryOptFc() (ast.Fc, error) {
	unaryOp, err := tb.header.currentToken()
	if err != nil {
		return nil, err
	}
	if !glob.IsBuiltinUnaryOpt(unaryOp) {
		// return tb.fcAtomAndFcFn()
		return tb.squareBracketExpr()
	} else {
		tb.header.skip(unaryOp)

		right, err := tb.unaryOptFc()
		if err != nil {
			return nil, err
		}

		leftHead := ast.FcAtom(unaryOp)
		return ast.NewFcFn(
			leftHead,
			[]ast.Fc{right},
		), nil
	}
}

func (tb *tokenBlock) numberStr() (ast.FcAtom, error) {
	left, err := tb.header.next()
	if err != nil {
		return ast.EmptyFcAtom, err
	}

	// 检查left是否全是数字
	for _, c := range left {
		if c < '0' || c > '9' {
			return ast.EmptyFcAtom, fmt.Errorf("invalid number: %s", left)
		}
	}

	if tb.header.is(glob.KeySymbolDot) {
		// 检查下一个字符是否是数字
		nextChar := tb.header.strAtCurIndexPlus(1)
		if len(nextChar) == 0 {
			return ast.FcAtom(left), nil
		}

		allDigits := true
		for _, c := range nextChar {
			if c < '0' || c > '9' {
				allDigits = false
				break
			}
		}

		if allDigits {
			tb.header.skip("")
			right, err := tb.header.next()
			if err != nil {
				return ast.EmptyFcAtom, fmt.Errorf("invalid number: %s", right)
			}
			return ast.FcAtom(left + "." + right), nil
		}
		return ast.FcAtom(left), nil
	}

	return ast.FcAtom(left), nil
}

func (tb *tokenBlock) bracedFcSlice() ([]ast.Fc, error) {
	params := []ast.Fc{}
	tb.header.skip(glob.KeySymbolLeftBrace)

	if !tb.header.is(glob.KeySymbolRightBrace) {
		for {
			fc, err := tb.RawFc()

			if err != nil {
				return nil, tbErr(err, tb)
			}

			params = append(params, fc)

			if tb.header.is(glob.KeySymbolComma) {
				tb.header.skip(glob.KeySymbolComma)
				continue
			}

			if tb.header.is(glob.KeySymbolRightBrace) {
				break
			}

			return nil, tbErr(fmt.Errorf("expected ',' or '%s' but got '%s'", glob.KeySymbolRightBrace, tb.header.strAtCurIndexPlus(0)), tb)
		}
	}

	tb.header.skip(glob.KeySymbolRightBrace)

	return params, nil
}

func (tb *tokenBlock) bracedExpr() (ast.Fc, error) {
	tb.header.skip(glob.KeySymbolLeftBrace)
	if tb.header.ExceedEnd() {
		return nil, fmt.Errorf("unexpected end of input after '('")
	}

	// head, err := tb.fcInfixExpr(glob.PrecLowest)
	head, err := tb.RawFc()
	if err != nil {
		return nil, err
	}

	if tb.header.ExceedEnd() {
		return nil, fmt.Errorf("unexpected end of input, expected ')'")
	}

	if err := tb.header.skip(glob.KeySymbolRightBrace); err != nil {
		return nil, fmt.Errorf("expected '%s': %v", glob.KeySymbolRightBrace, err)
	}

	if !tb.header.is(glob.KeySymbolLeftBrace) {
		return head, nil
	}

	return head, nil

	// segs := [][]ast.Fc{}

	// for !tb.header.ExceedEnd() {
	// 	seg, err := tb.bracedFcSlice()
	// 	if err != nil {
	// 		return nil, &strSliceError{err, tb}
	// 	}
	// 	segs = append(segs, seg)
	// }

	// var curHead ast.Fc = head
	// for _, seg := range segs {
	// 	curHead = ast.NewFcFn(curHead, seg, nil)
	// }

	// return curHead, nil
}

func (tb *tokenBlock) consumeBracedFc(head ast.Fc) (ast.Fc, error) {
	for !tb.header.ExceedEnd() && (tb.header.is(glob.KeySymbolLeftBrace)) {
		objParamsPtr, err := tb.bracedFcSlice()
		if err != nil {
			return nil, tbErr(err, tb)
		}
		head = ast.NewFcFn(head, objParamsPtr)
	}

	return head, nil
}

func (tb *tokenBlock) fnSet() (ast.Fc, error) {
	tb.header.skip(glob.KeywordFn)
	tb.header.skip(glob.KeySymbolLeftBrace)

	fnSets := []ast.Fc{}
	var retSet ast.Fc
	for !tb.header.ExceedEnd() && !(tb.header.is(glob.KeySymbolRightBrace)) {
		fnSet, err := tb.RawFc()
		if err != nil {
			return nil, tbErr(err, tb)
		}
		fnSets = append(fnSets, fnSet)
		if tb.header.is(glob.KeySymbolComma) {
			tb.header.skip(glob.KeySymbolComma)
			continue
		}
	}

	err := tb.header.skip(glob.KeySymbolRightBrace)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	retSet, err = tb.RawFc()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	ret := ast.MakeFnSetFc(fnSets, retSet)

	return ret, nil
}

func ParseSourceCodeGetFc(s string) (ast.Fc, error) {
	blocks, err := makeTokenBlocks([]string{s})
	if err != nil {
		return nil, err
	}

	fc, err := blocks[0].RawFc()
	if err != nil {
		return nil, err
	}

	return fc, nil
}
