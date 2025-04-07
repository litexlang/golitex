package litexparser

import (
	"fmt"
	ast "golitex/litex_ast"
	glob "golitex/litex_global"
	"strconv"
)

func (parser *StrSliceCursor) parseFcAtomAndFcFnRetAndBracedFc() (ast.Fc, error) {
	if parser.is(glob.KeywordLeftParen) {
		return parser.parseBracedFcExpr()
	}

	if parser.curTokenBeginWithNumber() {
		return parser.parseNumberStr()
	}

	fcStr, err := parser.parseFcAtom()
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	strAtSecondPosition := parser.strAtCurIndexPlus(0)

	if strAtSecondPosition != glob.KeywordLeftParen {
		return &fcStr, nil
	} else {
		return parser.parseFcFnRetVal(fcStr)
	}
}

func (parser *StrSliceCursor) parseBracedFcExpr() (ast.Fc, error) {
	parser.skip(glob.KeywordLeftParen)
	fc, err := parser.ParseFc()
	if err != nil {
		return nil, &parserErr{err, parser}
	}
	parser.skip(glob.KeywordRightParen)
	return fc, nil
}

func (parser *StrSliceCursor) parseFcFnRetVal(optName ast.FcAtom) (*ast.FcFnPipe, error) {
	typeParamsObjParamsPairs, err := parser.parseTypeParamsObjParamsPairs()

	if err != nil {
		return nil, err
	}

	return ast.MakeFcFnPipe(optName, typeParamsObjParamsPairs), nil
	// return &ast.FcFnPipe{optName, typeParamsObjParamsPairs}, nil
}

func (parser *StrSliceCursor) parseTypeParamsObjParamsPairs() ([]*ast.FcFnPipeSeg, error) {
	pairs := []*ast.FcFnPipeSeg{}

	for !parser.ExceedEnd() && (parser.is(glob.KeywordLeftParen)) {
		objParamsPtr, err := parser.parseBracedFcArr()
		if err != nil {
			return nil, &parserErr{err, parser}
		}

		// pairs = append(pairs, {objParamsPtr})
		// pairs = append(pairs, &ast.FcFnPipeSeg{objParamsPtr})
		pairs = append(pairs, ast.MakeFcFnPipeSeg(objParamsPtr))
	}

	return pairs, nil
}

func (parser *StrSliceCursor) parseFcAtom() (ast.FcAtom, error) {
	value, err := parser.next()
	if err != nil {
		return ast.FcAtom{Value: ""}, err
	}

	fromPkg := ""
	if parser.is(glob.KeywordColonColon) {
		fromPkg = value
		err := parser.skip(glob.KeywordColonColon)
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

func (parser *StrSliceCursor) ParseFc() (ast.Fc, error) {
	return parser.parseFcInfixExpr(glob.PrecLowest)
}

func (parser *StrSliceCursor) parseFcInfixExpr(currentPrec glob.FcInfixOptPrecedence) (ast.Fc, error) {
	left, err := parser.parseFcUnaryExpr()
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	for !parser.ExceedEnd() {
		curToken, err := parser.currentToken()
		if err != nil {
			return nil, err // 捕获错误并退出
		}

		if !glob.IsBuiltinRelaFn(curToken) {
			break // 不是内置运算符，跳出循环
		}

		curPrec, isBinary := glob.PrecedenceMap[curToken]
		if !isBinary || curPrec <= currentPrec {
			break
		}

		parser.skip() // 消耗运算符
		right, err := parser.parseFcInfixExpr(curPrec)
		if err != nil {
			return nil, &parserErr{err, parser}
		}

		leftHead := ast.MakeFcAtom("", curToken)

		left = ast.MakeFcFnPipe(
			*leftHead,
			[]*ast.FcFnPipeSeg{ast.MakeFcFnPipeSeg([]ast.Fc{left, right})},
			// []*ast.FcFnPipeSeg{{Params: []ast.Fc{left, right}}},
		)
	}

	return left, nil
}

func (parser *StrSliceCursor) parseFcUnaryExpr() (ast.Fc, error) {
	unaryOp, err := parser.currentToken()
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	if prec, isUnary := glob.UnaryPrecedence[unaryOp]; isUnary {
		parser.skip()
		right, err := parser.parseFcInfixExpr(prec)
		if err != nil {
			return nil, err
		}
		return &ast.FcFnPipe{
			FnHead:   ast.FcAtom{Value: unaryOp},
			CallPipe: []*ast.FcFnPipeSeg{{Params: []ast.Fc{right}}},
		}, nil
		// return ast.MakeFcFnPipe(*ast.MakeFcAtom("", unaryOp), []*ast.FcFnPipeSeg{ast.MakeFcFnPipeSeg([]ast.Fc{right})})
	} else {
		return parser.parseFcAtomAndFcFnRetAndBracedFc()
	}

}

func (parser *StrSliceCursor) parseNumberStr() (*ast.FcAtom, error) {
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

	if parser.is(glob.KeywordDot) {
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
