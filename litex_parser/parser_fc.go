// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen (malloc_realloc_calloc@outlook.com)
// Visit litexlang.org and https://github.com/litexlang/golitex for more information.

package litex_parser

import (
	"fmt"
	ast "golitex/litex_ast"
	glob "golitex/litex_global"
)

func (cursor *strSliceCursor) fcAtomAndFcFnRetAndBracedFc() (ast.Fc, error) {
	if cursor.is(glob.KeySymbolLeftBrace) {
		return cursor.bracedFcExpr()
	}

	if cursor.curTokenBeginWithNumber() {
		return cursor.numberStr()
	}

	fcStr, err := cursor.rawFcAtom()
	if err != nil {
		return nil, &strSliceErr{err, cursor}
	}

	strAtSecondPosition := cursor.strAtCurIndexPlus(0)

	if strAtSecondPosition != glob.KeySymbolLeftBrace {
		return &fcStr, nil
	} else {
		return cursor.rawFcFn(fcStr)
	}
}

func (cursor *strSliceCursor) bracedFcExpr() (ast.Fc, error) {
	cursor.skip(glob.KeySymbolLeftBrace)
	fc, err := cursor.rawFc()
	if err != nil {
		return nil, &strSliceErr{err, cursor}
	}
	cursor.skip(glob.KeySymbolRightBrace)
	return fc, nil
}

func (cursor *strSliceCursor) rawFcFn(optName ast.FcAtom) (*ast.FcFn, error) {
	typeParamsObjParamsPairs, err := cursor.objSetPairs()

	if err != nil {
		return nil, err
	}

	return ast.NewFcFnPipe(optName, typeParamsObjParamsPairs), nil
}

func (cursor *strSliceCursor) objSetPairs() ([]*ast.FcFnSeg, error) {
	pairs := []*ast.FcFnSeg{}

	for !cursor.ExceedEnd() && (cursor.is(glob.KeySymbolLeftBrace)) {
		objParamsPtr, err := cursor.bracedFcSlice()
		if err != nil {
			return nil, &strSliceErr{err, cursor}
		}

		pairs = append(pairs, ast.NewFcFnPipeSeg(objParamsPtr))
	}

	return pairs, nil
}

func (cursor *strSliceCursor) rawFcAtom() (ast.FcAtom, error) {
	value, err := cursor.next()
	if err != nil {
		return ast.FcAtom{Value: ""}, err
	}

	fromPkg := ""
	if cursor.is(glob.KeySymbolColonColon) {
		fromPkg = value
		err := cursor.skip(glob.KeySymbolColonColon)
		if err != nil {
			return ast.FcAtom{Value: ""}, err
		}
		value, err = cursor.next()
		if err != nil {
			return ast.FcAtom{Value: ""}, err
		}
	}

	return ast.FcAtom{PkgName: fromPkg, Value: value}, nil
}

func (cursor *strSliceCursor) rawFc() (ast.Fc, error) {
	expr, err := cursor.fcInfixExpr(glob.PrecLowest)
	if err != nil {
		return nil, err
	}
	return expr, nil
}

func (cursor *strSliceCursor) fcInfixExpr(currentPrec glob.BuiltinOptPrecedence) (ast.Fc, error) {
	left, err := cursor.fcPrimaryExpr()
	if err != nil {
		return nil, err
	}

	for !cursor.ExceedEnd() {
		curToken, err := cursor.currentToken()
		if err != nil {
			return nil, fmt.Errorf("unexpected end of input while parsing infix expression")
		}

		// 检查是否是运算符
		curPrec, isBinary := glob.BuiltinOptPrecedenceMap[curToken]
		if !isBinary || curPrec <= currentPrec {
			break
		}

		cursor.skip() // 消耗运算符
		right, err := cursor.fcInfixExpr(curPrec)
		if err != nil {
			return nil, err
		}

		leftHead := ast.NewFcAtom("", curToken)
		left = ast.NewFcFnPipe(
			*leftHead,
			[]*ast.FcFnSeg{ast.NewFcFnPipeSeg([]ast.Fc{left, right})},
		)
	}

	return left, nil
}

func (cursor *strSliceCursor) fcPrimaryExpr() (ast.Fc, error) {
	if cursor.ExceedEnd() {
		return nil, fmt.Errorf("unexpected end of input, expected expression")
	}

	// 处理括号表达式
	if cursor.is(glob.KeySymbolLeftBrace) {
		cursor.skip(glob.KeySymbolLeftBrace)
		if cursor.ExceedEnd() {
			return nil, fmt.Errorf("unexpected end of input after '('")
		}

		expr, err := cursor.fcInfixExpr(glob.PrecLowest)
		if err != nil {
			return nil, err
		}

		if cursor.ExceedEnd() {
			return nil, fmt.Errorf("unexpected end of input, expected ')'")
		}

		if err := cursor.skip(glob.KeySymbolRightBrace); err != nil {
			return nil, fmt.Errorf("expected ')': %v", err)
		}
		return expr, nil
	}

	return cursor.unaryOptFc()
	// fc, isUnary, err := cursor.unaryOptFc()
	// if err != nil {
	// 	return nil, err
	// }
	// if isUnary {
	// 	return fc, nil
	// }

	// // 处理基本原子表达式
	// return cursor.fcAtomAndFcFnRetAndBracedFc()
}

func (cursor *strSliceCursor) unaryOptFc() (ast.Fc, error) {
	unaryOp, err := cursor.currentToken()
	if err != nil {
		return nil, err
	}
	if !glob.IsKeySymbolUniFn(unaryOp) {
		return cursor.fcAtomAndFcFnRetAndBracedFc()
	} else {
		cursor.skip(unaryOp)

		right, err := cursor.fcPrimaryExpr()
		if err != nil {
			return nil, err
		}

		leftHead := ast.NewFcAtom(glob.BuiltinUnaryPkgName, glob.KeySymbolMinus)
		return ast.NewFcFnPipe(
			*leftHead,
			[]*ast.FcFnSeg{ast.NewFcFnPipeSeg([]ast.Fc{right})},
		), nil
	}
}

func (cursor *strSliceCursor) numberStr() (*ast.FcAtom, error) {
	left, err := cursor.next()
	if err != nil {
		return &ast.FcAtom{Value: ""}, err
	}

	// 检查left是否全是数字
	for _, c := range left {
		if c < '0' || c > '9' {
			return &ast.FcAtom{Value: ""}, fmt.Errorf("invalid number: %s", left)
		}
	}

	if cursor.is(glob.KeySymbolDot) {
		// 检查下一个字符是否是数字
		nextChar := cursor.strAtCurIndexPlus(1)
		if len(nextChar) == 0 {
			return &ast.FcAtom{Value: left}, nil
		}

		allDigits := true
		for _, c := range nextChar {
			if c < '0' || c > '9' {
				allDigits = false
				break
			}
		}

		if allDigits {
			cursor.skip()
			right, err := cursor.next()
			if err != nil {
				return &ast.FcAtom{Value: ""}, fmt.Errorf("invalid number: %s", right)
			}
			return &ast.FcAtom{Value: left + "." + right}, nil
		}
		return &ast.FcAtom{Value: left}, nil
	}

	return &ast.FcAtom{Value: left}, nil
}

func (cursor *strSliceCursor) bracedFcSlice() ([]ast.Fc, error) {
	params := []ast.Fc{}
	cursor.skip(glob.KeySymbolLeftBrace)

	for !cursor.is(glob.KeySymbolRightBrace) {
		fc, err := cursor.rawFc()

		if err != nil {
			return nil, &strSliceErr{err, cursor}
		}

		params = append(params, fc)

		cursor.skipIfIs(glob.KeySymbolComma)
	}

	cursor.skip(glob.KeySymbolRightBrace)

	return params, nil
}

func (cursor *strSliceCursor) paramSliceInDeclHeadAndSkipEnd(endWith string) ([]string, []ast.Fc, error) {
	paramName := []string{}
	paramTypes := []ast.Fc{}

	for !cursor.is(endWith) {
		objName, err := cursor.next()
		if err != nil {
			return nil, nil, &strSliceErr{err, cursor}
		}

		tp, err := cursor.rawFc()
		if err != nil {
			return nil, nil, &strSliceErr{err, cursor}
		}

		paramName = append(paramName, objName)
		paramTypes = append(paramTypes, tp)

		cursor.skipIfIs(glob.KeySymbolComma)
	}

	if cursor.isAndSkip(endWith) {
		return paramName, paramTypes, nil
	} else {
		return nil, nil, &strSliceErr{fmt.Errorf("expected '%s' but got '%s'", endWith, cursor.strAtCurIndexPlus(0)), cursor}
	}
}

func (cursor *strSliceCursor) stringSliceUntilEnd() ([]string, error) {
	members := []string{}

	for {
		member, err := cursor.next()
		if err != nil {
			return nil, &strSliceErr{err, cursor}
		}
		members = append(members, member)
		if !cursor.is(glob.KeySymbolComma) {
			break
		}
		cursor.skip()
	}

	if !cursor.ExceedEnd() {
		return nil, &strSliceErr{fmt.Errorf("expected comma or end of string array"), cursor}
	}

	return members, nil
}

func (cursor *strSliceCursor) isExpr(left ast.Fc) (*ast.SpecFactStmt, error) {
	err := cursor.skip(glob.KeywordIs)
	if err != nil {
		return nil, &strSliceErr{err, cursor}
	}

	opt, err := cursor.rawFcAtom() // get the operator.

	if err != nil {
		return nil, &strSliceErr{err, cursor}
	}

	return ast.NewSpecFactStmt(true, opt, []ast.Fc{left}), nil
	// return &ast.SpecFactStmt{true, opt, []ast.Fc{left}}, nil
}

func (cursor *strSliceCursor) typeListInDeclsAndSkipEnd(endWith string) ([]string, []*ast.FcAtom, error) {
	paramName := []string{}
	paramTypes := []*ast.FcAtom{}

	for !cursor.is(endWith) {
		objName, err := cursor.next()
		if err != nil {
			return nil, nil, &strSliceErr{err, cursor}
		}

		tp, err := cursor.rawFcAtom()
		if err != nil {
			return nil, nil, &strSliceErr{err, cursor}
		}

		paramName = append(paramName, objName)
		paramTypes = append(paramTypes, &tp)

		cursor.skipIfIs(glob.KeySymbolComma)
	}

	if cursor.isAndSkip(endWith) {
		return paramName, paramTypes, nil
	} else {
		return nil, nil, &strSliceErr{fmt.Errorf("expected '%s' but got '%s'", endWith, cursor.strAtCurIndexPlus(0)), cursor}
	}
}
