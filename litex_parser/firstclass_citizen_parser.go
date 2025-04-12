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
		return nil, &parserErr{err, parser}
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
		return nil, &parserErr{err, parser}
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
			return nil, &parserErr{err, parser}
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

	// 处理一元运算符
	fc, isUnary, err := parser.unaryOptFc()
	if err != nil {
		return nil, err
	}
	if isUnary {
		return fc, nil
	}

	// 处理基本原子表达式
	return parser.fcAtomAndFcFnRetAndBracedFc()
}

func (parser *strSliceCursor) unaryOptFc() (*ast.FcFn, bool, error) {
	unaryOp, err := parser.currentToken()
	if err != nil {
		return nil, false, err
	}

	parser.skip(unaryOp)

	right, err := parser.fcPrimaryExpr()
	if err != nil {
		return nil, false, err
	}

	if unaryOp == glob.KeySymbolMinus {
		leftHead := ast.NewFcAtom(glob.BuiltinPrefixOptPkg, glob.KeySymbolMinus)
		return ast.NewFcFnPipe(
			*leftHead,
			[]*ast.FcFnSeg{ast.NewFcFnPipeSeg([]ast.Fc{&ast.FcFn{}, right})},
		), true, nil
	}

	return nil, false, fmt.Errorf("unexpected unary operator: %s", unaryOp)
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
