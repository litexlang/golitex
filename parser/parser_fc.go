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
// Litex Zulip community: https://litex.zulipchat.com

package litex_parser

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
	"strings"
)

func (cursor *strSliceCursor) RawFc() (ast.Fc, error) {
	expr, err := cursor.fcInfixExpr(glob.PrecLowest)
	if err != nil {
		return nil, err
	}
	return expr, nil
}

func (cursor *strSliceCursor) squareBracketExpr() (ast.Fc, error) {
	fc, err := cursor.fcAtomAndFcFn()
	if err != nil {
		return nil, err
	}

	if !cursor.is(glob.KeySymbolLeftSquareBrace) {
		return fc, nil
	}

	cursor.skip(glob.KeySymbolLeftSquareBrace)

	isAtIndexOp := true

	if cursor.is(glob.KeySymbolLeftSquareBrace) {
		cursor.skip(glob.KeySymbolLeftSquareBrace)
		isAtIndexOp = false
	}

	if cursor.ExceedEnd() {
		return nil, fmt.Errorf("unexpected end of input after '['")
	}

	fcInBracket, err := cursor.RawFc()
	if err != nil {
		return nil, err
	}

	if cursor.ExceedEnd() {
		return nil, fmt.Errorf("unexpected end of input after ']'")
	}

	if isAtIndexOp {
		if err := cursor.skip(glob.KeySymbolRightSquareBrace); err != nil {
			return nil, fmt.Errorf("expected '%s': %v", glob.KeySymbolRightSquareBrace, err)
		}

		return ast.NewFcFn(ast.NewFcAtomWithName(glob.AtIndexOp), []ast.Fc{fc, fcInBracket}), nil
	} else {
		if err := cursor.skip(glob.KeySymbolRightSquareBrace); err != nil {
			return nil, fmt.Errorf("expected '%s': %v", glob.KeySymbolRightSquareBrace, err)
		}

		if err := cursor.skip(glob.KeySymbolRightSquareBrace); err != nil {
			return nil, fmt.Errorf("expected '%s': %v", glob.KeySymbolRightSquareBrace, err)
		}

		return ast.NewFcFn(ast.NewFcAtomWithName(glob.GetIndexOfOp), []ast.Fc{fc, fcInBracket}), nil
	}
}

// “数学”优先级越高，越是底层。所以把括号表达式放在这里处理
func (cursor *strSliceCursor) fcAtomAndFcFn() (ast.Fc, error) {
	var expr ast.Fc
	var err error

	if cursor.is(glob.KeywordFn) {
		return cursor.fnSet()
	} else if cursor.is(glob.KeySymbolLeftBrace) {
		expr, err = cursor.bracedExpr()
		if err != nil {
			return nil, err
		}
		return cursor.consumeBracedFc(expr)
	} else if cursor.curTokenBeginWithNumber() {
		expr, err = cursor.numberStr()
		if err != nil {
			return nil, err
		}
		if cursor.is(glob.KeySymbolLeftBrace) {
			return nil, fmt.Errorf("unexpected left brace after number")
		} else {
			return expr, nil
		}
	} else {
		fcStr, err := cursor.rawFcAtom()
		if err != nil {
			return nil, &strSliceErr{err, cursor}
		}
		ret, err := cursor.consumeBracedFc(fcStr)
		if err != nil {
			return nil, &strSliceErr{err, cursor}
		}
		// dot
		if cursor.is(glob.KeySymbolDot) {
			cursor.skip(glob.KeySymbolDot)
			dotFc, err := cursor.rawFcAtom()
			if err != nil {
				return nil, &strSliceErr{err, cursor}
			}
			ret = ast.NewFcFn(ast.NewFcAtomWithName(glob.KeySymbolDot), []ast.Fc{ret, dotFc})
		}
		return ret, nil
	}
}

// func (cursor *strSliceCursor) rawFcFn(optName ast.Fc) (ast.Fc, error) {
// 	typeParamsObjParamsPairs, err := cursor.fcFnSegs()

// 	if err != nil {
// 		return nil, err
// 	}

// 	var curHead ast.Fc = optName
// 	for _, seg := range typeParamsObjParamsPairs {
// 		curHead = ast.NewFcFn(curHead, seg, nil)
// 	}

// 	return curHead, nil
// }

// func (cursor *strSliceCursor) fcFnSegs() ([][]ast.Fc, error) {
// 	params := [][]ast.Fc{}

// 	for !cursor.ExceedEnd() && (cursor.is(glob.KeySymbolLeftBrace)) {
// 		objParamsPtr, err := cursor.bracedFcSlice()
// 		if err != nil {
// 			return nil, &strSliceErr{err, cursor}
// 		}

// 		params = append(params, (objParamsPtr))
// 	}

// 	return params, nil
// }

func (cursor *strSliceCursor) rawFcAtom() (*ast.FcAtom, error) {
	value, err := cursor.next()
	if err != nil {
		return nil, err
	}

	var pkgName strings.Builder
	if cursor.is(glob.KeySymbolColonColon) {
		pkgName.WriteString(value)
		value, err = cursor.next()
		if err != nil {
			return nil, err
		}
	}

	pkgNameStr := pkgName.String()

	// TODO: 在parse时，把pkgName改成当前项目里定义的 pkgName，而不是继续沿用原来的
	// REMARK: 我需要一个全局变量，来记录当前项目里定义的 pkgName
	// if realPkgName, ok := cursor.parserEnv.PkgManagementMap[pkgNameStr]; ok {
	// 	pkgNameStr = realPkgName
	// }

	if glob.IsBuiltinKeywordKeySymbol_NeverBeFcAtom(value) {
		return ast.NewFcAtom(pkgNameStr, value), fmt.Errorf("invalid first citizen: %s", value)
	} else {
		return ast.NewFcAtom(pkgNameStr, value), nil
	}
}

func (cursor *strSliceCursor) fcInfixExpr(currentPrec glob.BuiltinOptPrecedence) (ast.Fc, error) {
	left, err := cursor.unaryOptFc()
	if err != nil {
		return nil, err
	}

	for !cursor.ExceedEnd() {
		curToken, err := cursor.currentToken()
		if err != nil {
			return nil, fmt.Errorf("unexpected end of input while parsing infix expression")
		}

		if curToken == glob.RelaFnPrefix {
			cursor.skip("") // 消耗curToken

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

		cursor.skip("") // 消耗运算符
		right, err := cursor.fcInfixExpr(curPrec)
		if err != nil {
			return nil, err
		}

		leftHead := ast.NewFcAtomWithName(curToken)
		left = ast.NewFcFn(
			leftHead,
			[]ast.Fc{left, right},
		)
	}

	return left, nil
}

// func (cursor *strSliceCursor) fcPrimaryExpr() (ast.Fc, error) {
// 	if cursor.ExceedEnd() {
// 		return nil, fmt.Errorf("unexpected end of input, expected expression")
// 	}

// 	return cursor.unaryOptFc()
// }

func (cursor *strSliceCursor) unaryOptFc() (ast.Fc, error) {
	unaryOp, err := cursor.currentToken()
	if err != nil {
		return nil, err
	}
	if !glob.IsBuiltinUnaryOpt(unaryOp) {
		// return cursor.fcAtomAndFcFn()
		return cursor.squareBracketExpr()
	} else {
		cursor.skip(unaryOp)

		right, err := cursor.unaryOptFc()
		if err != nil {
			return nil, err
		}

		leftHead := ast.NewFcAtomWithName(unaryOp)
		return ast.NewFcFn(
			leftHead,
			[]ast.Fc{right},
		), nil
	}
}

func (cursor *strSliceCursor) numberStr() (*ast.FcAtom, error) {
	left, err := cursor.next()
	if err != nil {
		return &ast.EmptyFcAtom, err
	}

	// 检查left是否全是数字
	for _, c := range left {
		if c < '0' || c > '9' {
			return &ast.EmptyFcAtom, fmt.Errorf("invalid number: %s", left)
		}
	}

	if cursor.is(glob.KeySymbolDot) {
		// 检查下一个字符是否是数字
		nextChar := cursor.strAtCurIndexPlus(1)
		if len(nextChar) == 0 {
			return ast.NewFcAtomWithName(left), nil
		}

		allDigits := true
		for _, c := range nextChar {
			if c < '0' || c > '9' {
				allDigits = false
				break
			}
		}

		if allDigits {
			cursor.skip("")
			right, err := cursor.next()
			if err != nil {
				return &ast.EmptyFcAtom, fmt.Errorf("invalid number: %s", right)
			}
			return ast.NewFcAtomWithName(left + "." + right), nil
		}
		return ast.NewFcAtomWithName(left), nil
	}

	return ast.NewFcAtomWithName(left), nil
}

func (cursor *strSliceCursor) bracedFcSlice() ([]ast.Fc, error) {
	params := []ast.Fc{}
	cursor.skip(glob.KeySymbolLeftBrace)

	if !cursor.is(glob.KeySymbolRightBrace) {
		for {
			fc, err := cursor.RawFc()

			if err != nil {
				return nil, &strSliceErr{err, cursor}
			}

			params = append(params, fc)

			if cursor.is(glob.KeySymbolComma) {
				cursor.skip(glob.KeySymbolComma)
				continue
			}

			if cursor.is(glob.KeySymbolRightBrace) {
				break
			}

			return nil, &strSliceErr{fmt.Errorf("expected ',' or '%s' but got '%s'", glob.KeySymbolRightBrace, cursor.strAtCurIndexPlus(0)), cursor}
		}
	}

	cursor.skip(glob.KeySymbolRightBrace)

	return params, nil
}

func (cursor *strSliceCursor) bracedExpr() (ast.Fc, error) {
	cursor.skip(glob.KeySymbolLeftBrace)
	if cursor.ExceedEnd() {
		return nil, fmt.Errorf("unexpected end of input after '('")
	}

	// head, err := cursor.fcInfixExpr(glob.PrecLowest)
	head, err := cursor.RawFc()
	if err != nil {
		return nil, err
	}

	if cursor.ExceedEnd() {
		return nil, fmt.Errorf("unexpected end of input, expected ')'")
	}

	if err := cursor.skip(glob.KeySymbolRightBrace); err != nil {
		return nil, fmt.Errorf("expected '%s': %v", glob.KeySymbolRightBrace, err)
	}

	if !cursor.is(glob.KeySymbolLeftBrace) {
		return head, nil
	}

	return head, nil

	// segs := [][]ast.Fc{}

	// for !cursor.ExceedEnd() {
	// 	seg, err := cursor.bracedFcSlice()
	// 	if err != nil {
	// 		return nil, &strSliceErr{err, cursor}
	// 	}
	// 	segs = append(segs, seg)
	// }

	// var curHead ast.Fc = head
	// for _, seg := range segs {
	// 	curHead = ast.NewFcFn(curHead, seg, nil)
	// }

	// return curHead, nil
}

func (cursor *strSliceCursor) consumeBracedFc(head ast.Fc) (ast.Fc, error) {
	for !cursor.ExceedEnd() && (cursor.is(glob.KeySymbolLeftBrace)) {
		objParamsPtr, err := cursor.bracedFcSlice()
		if err != nil {
			return nil, &strSliceErr{err, cursor}
		}
		head = ast.NewFcFn(head, objParamsPtr)
	}

	return head, nil
}

func (cursor *strSliceCursor) fnSet() (ast.Fc, error) {
	cursor.skip(glob.KeywordFn)
	cursor.skip(glob.KeySymbolLeftBrace)

	fnSets := []ast.Fc{}
	var retSet ast.Fc
	for !cursor.ExceedEnd() && !(cursor.is(glob.KeySymbolRightBrace)) {
		fnSet, err := cursor.RawFc()
		if err != nil {
			return nil, &strSliceErr{err, cursor}
		}
		fnSets = append(fnSets, fnSet)
		if cursor.is(glob.KeySymbolComma) {
			cursor.skip(glob.KeySymbolComma)
			continue
		}
	}

	err := cursor.skip(glob.KeySymbolRightBrace)
	if err != nil {
		return nil, &strSliceErr{err, cursor}
	}

	retSet, err = cursor.RawFc()
	if err != nil {
		return nil, &strSliceErr{err, cursor}
	}

	ret := ast.MakeFnSetFc(fnSets, retSet)

	return ret, nil
}

func ParseSourceCodeGetFc(s string) (ast.Fc, error) {
	blocks, err := makeTokenBlocks([]string{s})
	if err != nil {
		return nil, err
	}

	fc, err := blocks[0].header.RawFc()
	if err != nil {
		return nil, err
	}

	return fc, nil
}
