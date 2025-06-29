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

func (cursor *tokenBlock) RawFc() (ast.Fc, error) {
	expr, err := cursor.fcInfixExpr(glob.PrecLowest)
	if err != nil {
		return nil, err
	}

	if _, ok := expr.(*ast.FcAtom); ok {
		return expr, fmt.Errorf("invalid first citizen: %s", expr)
	}

	return expr, nil
}

func (cursor *tokenBlock) squareBracketExpr() (ast.Fc, error) {
	fc, err := cursor.fcAtomAndFcFn()
	if err != nil {
		return nil, err
	}

	if !cursor.header.is(glob.KeySymbolLeftBracket) {
		return fc, nil
	}

	cursor.header.skip(glob.KeySymbolLeftBracket)

	isAtIndexOp := true

	if cursor.header.is(glob.KeySymbolLeftBracket) {
		cursor.header.skip(glob.KeySymbolLeftBracket)
		isAtIndexOp = false
	}

	if cursor.header.ExceedEnd() {
		return nil, fmt.Errorf("unexpected end of input after '['")
	}

	fcInBracket, err := cursor.RawFc()
	if err != nil {
		return nil, err
	}

	if cursor.header.ExceedEnd() {
		return nil, fmt.Errorf("unexpected end of input after ']'")
	}

	if isAtIndexOp {
		if err := cursor.header.skip(glob.KeySymbolRightBracket); err != nil {
			return nil, fmt.Errorf("expected '%s': %v", glob.KeySymbolRightBracket, err)
		}

		return ast.NewFcFn(ast.FcAtom(glob.AtIndexOp), []ast.Fc{fc, fcInBracket}), nil
	} else {
		if err := cursor.header.skip(glob.KeySymbolRightBracket); err != nil {
			return nil, fmt.Errorf("expected '%s': %v", glob.KeySymbolRightBracket, err)
		}

		if err := cursor.header.skip(glob.KeySymbolRightBracket); err != nil {
			return nil, fmt.Errorf("expected '%s': %v", glob.KeySymbolRightBracket, err)
		}

		return ast.NewFcFn(ast.FcAtom(glob.GetIndexOfOp), []ast.Fc{fc, fcInBracket}), nil
	}
}

// “数学”优先级越高，越是底层。所以把括号表达式放在这里处理
func (cursor *tokenBlock) fcAtomAndFcFn() (ast.Fc, error) {
	var expr ast.Fc
	var err error

	if cursor.header.is(glob.KeywordFn) {
		return cursor.fnSet()
	} else if cursor.header.is(glob.KeySymbolLeftBrace) {
		expr, err = cursor.bracedExpr()
		if err != nil {
			return nil, err
		}
		return cursor.consumeBracedFc(expr)
	} else if cursor.header.curTokenBeginWithNumber() {
		expr, err = cursor.numberStr()
		if err != nil {
			return nil, err
		}
		if cursor.header.is(glob.KeySymbolLeftBrace) {
			return nil, fmt.Errorf("unexpected left brace after number")
		} else {
			return expr, nil
		}
	} else {
		fcStr, err := cursor.rawFcAtom()
		if err != nil {
			return nil, tbErr(err, cursor)
		}
		ret, err := cursor.consumeBracedFc(fcStr)
		if err != nil {
			return nil, tbErr(err, cursor)
		}
		// dot
		if cursor.header.is(glob.MemberAccessOpt) {
			cursor.header.skip(glob.MemberAccessOpt)
			dotFc, err := cursor.rawFcAtom()
			if err != nil {
				return nil, tbErr(err, cursor)
			}
			ret = ast.NewFcFn(ast.FcAtom(glob.MemberAccessOpt), []ast.Fc{ret, dotFc})
		}
		return ret, nil
	}
}

func (cursor *tokenBlock) rawFcAtom() (ast.FcAtom, error) {
	values := []string{}

	value, err := cursor.header.next()
	if err != nil {
		return ast.EmptyFcAtom, err
	}

	for cursor.header.is(glob.KeySymbolColonColon) {
		cursor.header.skip(glob.KeySymbolColonColon)
		values = append(values, value)
		value, err = cursor.header.next()
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

func (cursor *tokenBlock) fcInfixExpr(currentPrec glob.BuiltinOptPrecedence) (ast.Fc, error) {
	left, err := cursor.unaryOptFc()
	if err != nil {
		return nil, err
	}

	for !cursor.header.ExceedEnd() {
		curToken, err := cursor.header.currentToken()
		if err != nil {
			return nil, fmt.Errorf("unexpected end of input while parsing infix expression")
		}

		if curToken == glob.RelaFnPrefix {
			cursor.header.skip("") // 消耗curToken

			fn, err := cursor.RawFc()
			if err != nil {
				return nil, err
			}

			right, err := cursor.fcInfixExpr(glob.PrecLowest)
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

		cursor.header.skip("") // 消耗运算符
		right, err := cursor.fcInfixExpr(curPrec)
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

// func (cursor *tokenBlock) fcPrimaryExpr() (ast.Fc, error) {
// 	if cursor.ExceedEnd() {
// 		return nil, fmt.Errorf("unexpected end of input, expected expression")
// 	}

// 	return cursor.unaryOptFc()
// }

func (cursor *tokenBlock) unaryOptFc() (ast.Fc, error) {
	unaryOp, err := cursor.header.currentToken()
	if err != nil {
		return nil, err
	}
	if !glob.IsBuiltinUnaryOpt(unaryOp) {
		// return cursor.fcAtomAndFcFn()
		return cursor.squareBracketExpr()
	} else {
		cursor.header.skip(unaryOp)

		right, err := cursor.unaryOptFc()
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

func (cursor *tokenBlock) numberStr() (ast.FcAtom, error) {
	left, err := cursor.header.next()
	if err != nil {
		return ast.EmptyFcAtom, err
	}

	// 检查left是否全是数字
	for _, c := range left {
		if c < '0' || c > '9' {
			return ast.EmptyFcAtom, fmt.Errorf("invalid number: %s", left)
		}
	}

	if cursor.header.is(glob.KeySymbolDot) {
		// 检查下一个字符是否是数字
		nextChar := cursor.header.strAtCurIndexPlus(1)
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
			cursor.header.skip("")
			right, err := cursor.header.next()
			if err != nil {
				return ast.EmptyFcAtom, fmt.Errorf("invalid number: %s", right)
			}
			return ast.FcAtom(left + "." + right), nil
		}
		return ast.FcAtom(left), nil
	}

	return ast.FcAtom(left), nil
}

func (cursor *tokenBlock) bracedFcSlice() ([]ast.Fc, error) {
	params := []ast.Fc{}
	cursor.header.skip(glob.KeySymbolLeftBrace)

	if !cursor.header.is(glob.KeySymbolRightBrace) {
		for {
			fc, err := cursor.RawFc()

			if err != nil {
				return nil, tbErr(err, cursor)
			}

			params = append(params, fc)

			if cursor.header.is(glob.KeySymbolComma) {
				cursor.header.skip(glob.KeySymbolComma)
				continue
			}

			if cursor.header.is(glob.KeySymbolRightBrace) {
				break
			}

			return nil, tbErr(fmt.Errorf("expected ',' or '%s' but got '%s'", glob.KeySymbolRightBrace, cursor.header.strAtCurIndexPlus(0)), cursor)
		}
	}

	cursor.header.skip(glob.KeySymbolRightBrace)

	return params, nil
}

func (cursor *tokenBlock) bracedExpr() (ast.Fc, error) {
	cursor.header.skip(glob.KeySymbolLeftBrace)
	if cursor.header.ExceedEnd() {
		return nil, fmt.Errorf("unexpected end of input after '('")
	}

	// head, err := cursor.fcInfixExpr(glob.PrecLowest)
	head, err := cursor.RawFc()
	if err != nil {
		return nil, err
	}

	if cursor.header.ExceedEnd() {
		return nil, fmt.Errorf("unexpected end of input, expected ')'")
	}

	if err := cursor.header.skip(glob.KeySymbolRightBrace); err != nil {
		return nil, fmt.Errorf("expected '%s': %v", glob.KeySymbolRightBrace, err)
	}

	if !cursor.header.is(glob.KeySymbolLeftBrace) {
		return head, nil
	}

	return head, nil

	// segs := [][]ast.Fc{}

	// for !cursor.header.ExceedEnd() {
	// 	seg, err := cursor.bracedFcSlice()
	// 	if err != nil {
	// 		return nil, &strSliceError{err, cursor}
	// 	}
	// 	segs = append(segs, seg)
	// }

	// var curHead ast.Fc = head
	// for _, seg := range segs {
	// 	curHead = ast.NewFcFn(curHead, seg, nil)
	// }

	// return curHead, nil
}

func (cursor *tokenBlock) consumeBracedFc(head ast.Fc) (ast.Fc, error) {
	for !cursor.header.ExceedEnd() && (cursor.header.is(glob.KeySymbolLeftBrace)) {
		objParamsPtr, err := cursor.bracedFcSlice()
		if err != nil {
			return nil, tbErr(err, cursor)
		}
		head = ast.NewFcFn(head, objParamsPtr)
	}

	return head, nil
}

func (cursor *tokenBlock) fnSet() (ast.Fc, error) {
	cursor.header.skip(glob.KeywordFn)
	cursor.header.skip(glob.KeySymbolLeftBrace)

	fnSets := []ast.Fc{}
	var retSet ast.Fc
	for !cursor.header.ExceedEnd() && !(cursor.header.is(glob.KeySymbolRightBrace)) {
		fnSet, err := cursor.RawFc()
		if err != nil {
			return nil, tbErr(err, cursor)
		}
		fnSets = append(fnSets, fnSet)
		if cursor.header.is(glob.KeySymbolComma) {
			cursor.header.skip(glob.KeySymbolComma)
			continue
		}
	}

	err := cursor.header.skip(glob.KeySymbolRightBrace)
	if err != nil {
		return nil, tbErr(err, cursor)
	}

	retSet, err = cursor.RawFc()
	if err != nil {
		return nil, tbErr(err, cursor)
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
