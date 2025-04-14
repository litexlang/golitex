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

func (parser *strSliceCursor) fcAtomAndFcFnRetAndBracedFc() (ast.Fc, error) {
	if parser.is(glob.KeySymbolLeftBrace) {
		return parser.bracedFcExpr()
	}

	if parser.curTokenBeginWithNumber() {
		return parser.numberStr()
	}

	fcStr, err := parser.rawFcAtom()
	if err != nil {
		return nil, &strSliceErr{err, parser}
	}

	strAtSecondPosition := parser.strAtCurIndexPlus(0)

	if strAtSecondPosition != glob.KeySymbolLeftBrace {
		return &fcStr, nil
	} else {
		return parser.rawFcFn(fcStr)
	}
}

func (parser *strSliceCursor) bracedFcExpr() (ast.Fc, error) {
	parser.skip(glob.KeySymbolLeftBrace)
	fc, err := parser.rawFc()
	if err != nil {
		return nil, &strSliceErr{err, parser}
	}
	parser.skip(glob.KeySymbolRightBrace)
	return fc, nil
}

func (parser *strSliceCursor) rawFcFn(optName ast.FcAtom) (*ast.FcFn, error) {
	typeParamsObjParamsPairs, err := parser.objSetPairs()

	if err != nil {
		return nil, err
	}

	return ast.NewFcFnPipe(optName, typeParamsObjParamsPairs), nil
}

func (parser *strSliceCursor) objSetPairs() ([]*ast.FcFnSeg, error) {
	pairs := []*ast.FcFnSeg{}

	for !parser.ExceedEnd() && (parser.is(glob.KeySymbolLeftBrace)) {
		objParamsPtr, err := parser.bracedFcSlice()
		if err != nil {
			return nil, &strSliceErr{err, parser}
		}

		pairs = append(pairs, ast.NewFcFnPipeSeg(objParamsPtr))
	}

	return pairs, nil
}

func (parser *strSliceCursor) rawFcAtom() (ast.FcAtom, error) {
	value, err := parser.next()
	if err != nil {
		return ast.FcAtom{Value: ""}, err
	}

	fromPkg := ""
	if parser.is(glob.KeySymbolColonColon) {
		fromPkg = value
		err := parser.skip(glob.KeySymbolColonColon)
		if err != nil {
			return ast.FcAtom{Value: ""}, err
		}
		value, err = parser.next()
		if err != nil {
			return ast.FcAtom{Value: ""}, err
		}
	}

	return ast.FcAtom{PkgName: fromPkg, Value: value}, nil
}

func (parser *strSliceCursor) rawFc() (ast.Fc, error) {
	expr, err := parser.fcInfixExpr(glob.PrecLowest)
	if err != nil {
		return nil, err
	}
	return expr, nil
}

func (parser *strSliceCursor) fcInfixExpr(currentPrec glob.BuiltinOptPrecedence) (ast.Fc, error) {
	left, err := parser.fcPrimaryExpr()
	if err != nil {
		return nil, err
	}

	for !parser.ExceedEnd() {
		curToken, err := parser.currentToken()
		if err != nil {
			return nil, fmt.Errorf("unexpected end of input while parsing infix expression")
		}

		// 检查是否是运算符
		curPrec, isBinary := glob.BuiltinOptPrecedenceMap[curToken]
		if !isBinary || curPrec <= currentPrec {
			break
		}

		parser.skip() // 消耗运算符
		right, err := parser.fcInfixExpr(curPrec)
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

func (parser *strSliceCursor) fcPrimaryExpr() (ast.Fc, error) {
	if parser.ExceedEnd() {
		return nil, fmt.Errorf("unexpected end of input, expected expression")
	}

	// 处理括号表达式
	if parser.is(glob.KeySymbolLeftBrace) {
		parser.skip(glob.KeySymbolLeftBrace)
		if parser.ExceedEnd() {
			return nil, fmt.Errorf("unexpected end of input after '('")
		}

		expr, err := parser.fcInfixExpr(glob.PrecLowest)
		if err != nil {
			return nil, err
		}

		if parser.ExceedEnd() {
			return nil, fmt.Errorf("unexpected end of input, expected ')'")
		}

		if err := parser.skip(glob.KeySymbolRightBrace); err != nil {
			return nil, fmt.Errorf("expected ')': %v", err)
		}
		return expr, nil
	}

	return parser.unaryOptFc()
	// fc, isUnary, err := parser.unaryOptFc()
	// if err != nil {
	// 	return nil, err
	// }
	// if isUnary {
	// 	return fc, nil
	// }

	// // 处理基本原子表达式
	// return parser.fcAtomAndFcFnRetAndBracedFc()
}

func (parser *strSliceCursor) unaryOptFc() (ast.Fc, error) {
	unaryOp, err := parser.currentToken()
	if err != nil {
		return nil, err
	}
	if !glob.IsKeySymbolUniFn(unaryOp) {
		return parser.fcAtomAndFcFnRetAndBracedFc()
	} else {
		parser.skip(unaryOp)

		right, err := parser.fcPrimaryExpr()
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

func (parser *strSliceCursor) numberStr() (*ast.FcAtom, error) {
	left, err := parser.next()
	if err != nil {
		return &ast.FcAtom{Value: ""}, err
	}

	// 检查left是否全是数字
	for _, c := range left {
		if c < '0' || c > '9' {
			return &ast.FcAtom{Value: ""}, fmt.Errorf("invalid number: %s", left)
		}
	}

	if parser.is(glob.KeySymbolDot) {
		// 检查下一个字符是否是数字
		nextChar := parser.strAtCurIndexPlus(1)
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
			parser.skip()
			right, err := parser.next()
			if err != nil {
				return &ast.FcAtom{Value: ""}, fmt.Errorf("invalid number: %s", right)
			}
			return &ast.FcAtom{Value: left + "." + right}, nil
		}
		return &ast.FcAtom{Value: left}, nil
	}

	return &ast.FcAtom{Value: left}, nil
}

func (parser *strSliceCursor) bracedFcSlice() ([]ast.Fc, error) {
	params := []ast.Fc{}
	parser.skip(glob.KeySymbolLeftBrace)

	for !parser.is(glob.KeySymbolRightBrace) {
		fc, err := parser.rawFc()

		if err != nil {
			return nil, &strSliceErr{err, parser}
		}

		params = append(params, fc)

		if !parser.is(glob.KeySymbolComma) {
			if !parser.is(glob.KeySymbolRightBrace) {
				return nil, &strSliceErr{err, parser}
			} else {
				break
			}
		} else {
			parser.next()
		}

	}

	parser.skip(glob.KeySymbolRightBrace)

	return params, nil
}

func (parser *strSliceCursor) paramSliceInDeclHeadAndSkipEnd(endWith string) ([]string, []ast.Fc, error) {
	paramName := []string{}
	paramTypes := []ast.Fc{}

	for !parser.is(endWith) {
		objName, err := parser.next()
		if err != nil {
			return nil, nil, &strSliceErr{err, parser}
		}

		tp, err := parser.rawFc()
		if err != nil {
			return nil, nil, &strSliceErr{err, parser}
		}

		paramName = append(paramName, objName)
		paramTypes = append(paramTypes, tp)

		if parser.is(glob.KeySymbolComma) {
			parser.skip(glob.KeySymbolComma)
		}
	}

	if parser.isAndSkip(endWith) {
		return paramName, paramTypes, nil
	} else {
		return nil, nil, &strSliceErr{fmt.Errorf("expected '%s' but got '%s'", endWith, parser.strAtCurIndexPlus(0)), parser}
	}
}

func (parser *strSliceCursor) stringSliceUntilEnd() ([]string, error) {
	members := []string{}

	for {
		member, err := parser.next()
		if err != nil {
			return nil, &strSliceErr{err, parser}
		}
		members = append(members, member)
		if !parser.is(glob.KeySymbolComma) {
			break
		}
		parser.skip()
	}

	if !parser.ExceedEnd() {
		return nil, &strSliceErr{fmt.Errorf("expected comma or end of string array"), parser}
	}

	return members, nil
}

func (parser *strSliceCursor) isExpr(left ast.Fc) (*ast.SpecFactStmt, error) {
	err := parser.skip(glob.KeywordIs)
	if err != nil {
		return nil, &strSliceErr{err, parser}
	}

	opt, err := parser.rawFcAtom() // get the operator.

	if err != nil {
		return nil, &strSliceErr{err, parser}
	}

	return ast.NewSpecFactStmt(true, opt, []ast.Fc{left}), nil
	// return &ast.SpecFactStmt{true, opt, []ast.Fc{left}}, nil
}

func (parser *strSliceCursor) typeListInDeclsAndSkipEnd(endWith string) ([]string, []*ast.FcAtom, error) {
	paramName := []string{}
	paramTypes := []*ast.FcAtom{}

	for !parser.is(endWith) {
		objName, err := parser.next()
		if err != nil {
			return nil, nil, &strSliceErr{err, parser}
		}

		tp, err := parser.rawFcAtom()
		if err != nil {
			return nil, nil, &strSliceErr{err, parser}
		}

		paramName = append(paramName, objName)
		paramTypes = append(paramTypes, &tp)

		if parser.isAndSkip(endWith) {
			break
		}

		if err := parser.testAndSkip(glob.KeySymbolComma); err != nil {
			return nil, nil, &strSliceErr{err, parser}
		}
	}

	return paramName, paramTypes, nil
}
