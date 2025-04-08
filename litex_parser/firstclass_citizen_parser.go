package litex_parser

import (
	"fmt"
	ast "golitex/litex_ast"
	glob "golitex/litex_global"
	"strconv"
)

func (parser *StrSliceCursor) fcAtomAndFcFnRetAndBracedFc() (ast.Fc, error) {
	if parser.is(glob.KeySymbolLeftParen) {
		return parser.bracedFcExpr()
	}

	if parser.curTokenBeginWithNumber() {
		return parser.numberStr()
	}

	fcStr, err := parser.fcAtom()
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	strAtSecondPosition := parser.strAtCurIndexPlus(0)

	if strAtSecondPosition != glob.KeySymbolLeftParen {
		return &fcStr, nil
	} else {
		return parser.fcFnRetVal(fcStr)
	}
}

func (parser *StrSliceCursor) bracedFcExpr() (ast.Fc, error) {
	parser.skip(glob.KeySymbolLeftParen)
	fc, err := parser.Fc()
	if err != nil {
		return nil, &parserErr{err, parser}
	}
	parser.skip(glob.KeySymbolRightParen)
	return fc, nil
}

func (parser *StrSliceCursor) fcFnRetVal(optName ast.FcAtom) (*ast.FcFn, error) {
	typeParamsObjParamsPairs, err := parser.objSetPairs()

	if err != nil {
		return nil, err
	}

	return ast.NewFcFnPipe(optName, typeParamsObjParamsPairs), nil
	// return &ast.FcFnPipe{optName, typeParamsObjParamsPairs}, nil
}

func (parser *StrSliceCursor) objSetPairs() ([]*ast.FcFnSeg, error) {
	pairs := []*ast.FcFnSeg{}

	for !parser.ExceedEnd() && (parser.is(glob.KeySymbolLeftParen)) {
		objParamsPtr, err := parser.bracedFcSlice()
		if err != nil {
			return nil, &parserErr{err, parser}
		}

		// pairs = append(pairs, {objParamsPtr})
		// pairs = append(pairs, &ast.FcFnPipeSeg{objParamsPtr})
		pairs = append(pairs, ast.NewFcFnPipeSeg(objParamsPtr))
	}

	return pairs, nil
}

func (parser *StrSliceCursor) fcAtom() (ast.FcAtom, error) {
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

func (parser *StrSliceCursor) Fc() (ast.Fc, error) {
	return parser.fcInfixExpr(glob.PrecLowest)
}

func (parser *StrSliceCursor) fcInfixExpr(currentPrec glob.BuiltinOptPrecedence) (ast.Fc, error) {
	left, err := parser.fcUnaryExpr()
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	for !parser.ExceedEnd() {
		curToken, err := parser.currentToken()
		if err != nil {
			return nil, err // 捕获错误并退出
		}

		if !glob.IsKeySymbolRelaFn(curToken) {
			break // 不是内置运算符，跳出循环
		}

		curPrec, isBinary := glob.BuiltinOptPrecedenceMap[curToken]
		if !isBinary || curPrec <= currentPrec {
			break
		}

		parser.skip() // 消耗运算符
		right, err := parser.fcInfixExpr(curPrec)
		if err != nil {
			return nil, &parserErr{err, parser}
		}

		leftHead := ast.NewFcAtom("", curToken)

		left = ast.NewFcFnPipe(
			*leftHead,
			[]*ast.FcFnSeg{ast.NewFcFnPipeSeg([]ast.Fc{left, right})},
			// []*ast.FcFnPipeSeg{{Params: []ast.Fc{left, right}}},
		)
	}

	return left, nil
}

func (parser *StrSliceCursor) fcUnaryExpr() (ast.Fc, error) {
	unaryOp, err := parser.currentToken()
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	if prec, isUnary := glob.UnaryPrecedence[unaryOp]; isUnary {
		parser.skip()
		right, err := parser.fcInfixExpr(prec)
		if err != nil {
			return nil, err
		}
		return &ast.FcFn{
			FnHead:   ast.FcAtom{Value: unaryOp},
			CallPipe: []*ast.FcFnSeg{{Params: []ast.Fc{right}}},
		}, nil
		// return ast.MakeFcFnPipe(*ast.MakeFcAtom("", unaryOp), []*ast.FcFnPipeSeg{ast.MakeFcFnPipeSeg([]ast.Fc{right})})
	} else {
		return parser.fcAtomAndFcFnRetAndBracedFc()
	}

}

func (parser *StrSliceCursor) numberStr() (*ast.FcAtom, error) {
	left, err := parser.next()

	if err != nil {
		return &ast.FcAtom{Value: ""}, err
	}

	// if left[0] == '0' {
	// 	return &FcAtom{OptName: ""}, fmt.Errorf("invalid number, 0 is not allowed in the first position of a number")
	// }

	_, err = strconv.Atoi(left)
	if err != nil {
		return &ast.FcAtom{Value: ""}, fmt.Errorf("invalid number: %s", left)
	}

	if parser.is(glob.KeySymbolDot) {
		// The member after . might be a member or a number
		_, err := strconv.Atoi(parser.strAtCurIndexPlus(1))
		if err != nil {
			return &ast.FcAtom{Value: left}, err
		} else {
			parser.skip()
			right, err := parser.next()

			if err != nil {
				return &ast.FcAtom{Value: ""}, fmt.Errorf("invalid number: %s", right)
			}

			return &ast.FcAtom{Value: left + "." + right}, nil
		}
	}

	return &ast.FcAtom{Value: left}, nil
}
