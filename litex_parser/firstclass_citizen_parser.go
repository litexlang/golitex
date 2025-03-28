package litexparser

import (
	"fmt"
	"strconv"
)

func (parser *Parser) parseFcAtomAndFcFnRet() (Fc, error) {
	if parser.is(KeywordLeftParen) {
		return parser.parseBracedFcExpr()
	}

	if parser.curTokenBeginWithNumber() {
		return parser.parseNumberStr()
	}

	// TODO: 这里需要考虑xxx::yyy这种情况
	fcStr, err := parser.parseFcAtom()
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	strAtSecondPosition := parser.strAtCurIndexPlus(0)

	if strAtSecondPosition != KeywordLeftParen {
		return &fcStr, nil
	} else {
		return parser.parseFcFnRetVal(fcStr)
	}
}

// func (parser *Parser) parseFcChain(curFc FcChainMem) (*FcChain, error) {
// 	fcArr := []FcChainMem{curFc}
// 		err := error(nil)
// 	for !parser.ExceedEnd() && parser.is(KeywordDot) {
// 		err = parser.skip(KeywordDot)
// 		if err != nil {
// 			return nil, &parserErr{err, parser}
// 		}

// 		curFc, err = parser.parseFcChainMem()
// 		if err != nil {
// 			return nil, &parserErr{err, parser}
// 		}

// 		fcArr = append(fcArr, curFc)
// 	}

// 	ret := FcChain{fcArr}
// 	return &ret, nil
// }

func (parser *Parser) parseBracedFcExpr() (Fc, error) {
	parser.skip(KeywordLeftParen)
	fc, err := parser.ParseFc()
	if err != nil {
		return nil, &parserErr{err, parser}
	}
	parser.skip(KeywordRightParen)
	return fc, nil
}

// func (parser *Parser) parseFcChainMem() (FcChainMem, error) {
// 	// 如果 1 out of range了，那返回值是 “”
// 	strAtSecondPosition := parser.strAtCurIndexPlus(1)

// 	if strAtSecondPosition != KeywordLeftParen {
// 		return parser.parseFcStr()
// 	} else {
// 		return parser.parseFcFnRetVal()
// 	}
// }

func (parser *Parser) parseFcFnRetVal(optName FcAtom) (*FcFnCallPipe, error) {
	typeParamsObjParamsPairs, err := parser.parseTypeParamsObjParamsPairs()

	if err != nil {
		return nil, err
	}

	return &FcFnCallPipe{optName, *typeParamsObjParamsPairs}, nil
}

func (parser *Parser) parseTypeParamsObjParamsPairs() (*[]FcFnCallPipeSeg, error) {
	err := error(nil)

	pairs := []FcFnCallPipeSeg{}

	for !parser.ExceedEnd() && (parser.is(KeywordLeftParen)) {
		objParamsPtr := &[]Fc{}
		objParamsPtr, err = parser.parseBracedFcArr()
		if err != nil {
			return nil, &parserErr{err, parser}
		}

		pairs = append(pairs, FcFnCallPipeSeg{*objParamsPtr})
	}

	return &pairs, nil
}

func (parser *Parser) parseFcAtom() (FcAtom, error) {
	value, err := parser.next()
	if err != nil {
		return FcAtom{OptName: ""}, err
	}

	fromPkg := ""
	if parser.is(KeywordColonColon) {
		fromPkg = value
		err := parser.skip(KeywordColonColon)
		if err != nil {
			return FcAtom{OptName: ""}, err
		}
		value, err = parser.next()
		if err != nil {
			return FcAtom{OptName: ""}, err
		}
	}

	return FcAtom{PkgName: fromPkg, OptName: value}, nil
}

func (parser *Parser) ParseFc() (Fc, error) {
	return parser.parseFcInfixExpr(precLowest)
}

func (parser *Parser) parseFcInfixExpr(currentPrec FcInfixOptPrecedence) (Fc, error) {
	left, err := parser.parseFcUnaryExpr()
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	// process infix operators recursively
	for {
		curToken, err := parser.currentToken()
		if err != nil {
			return left, nil
		}

		curPrec, isBinary := precedenceMap[curToken]
		if !isBinary || curPrec <= currentPrec {
			break
		}

		parser.skip() // 消耗运算符
		right, err := parser.parseFcInfixExpr(curPrec)
		if err != nil {
			return nil, &parserErr{err, parser}
		}

		left = &FcFnCallPipe{
			FcAtom{OptName: curToken},
			[]FcFnCallPipeSeg{{[]Fc{left, right}}},
		}
	}

	return left, nil
}

func (parser *Parser) parseFcUnaryExpr() (Fc, error) {
	unaryOp, err := parser.currentToken()
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	if prec, isUnary := unaryPrecedence[unaryOp]; isUnary {
		parser.skip()
		right, err := parser.parseFcInfixExpr(prec)
		if err != nil {
			return nil, err
		}
		return &FcFnCallPipe{
			FcAtom{OptName: unaryOp},
			[]FcFnCallPipeSeg{{[]Fc{right}}},
		}, nil
	} else {
		return parser.parseFcAtomAndFcFnRet()
	}

}

func (parser *Parser) parseNumberStr() (*FcAtom, error) {
	left, err := parser.next()

	if err != nil {
		return &FcAtom{OptName: ""}, err
	}

	if left[0] == '0' {
		return &FcAtom{OptName: ""}, fmt.Errorf("invalid number, 0 is not allowed in the first position of a number")
	}

	_, err = strconv.Atoi(left)
	if err != nil {
		return &FcAtom{OptName: ""}, fmt.Errorf("invalid number: %s", left)
	}

	if parser.is(KeywordDot) {
		// The member after . might be a member or a number
		_, err := strconv.Atoi(parser.strAtCurIndexPlus(1))
		if err != nil {
			return &FcAtom{OptName: left}, nil
		} else {
			parser.skip()
			right, err := parser.next()

			if err != nil {
				return &FcAtom{OptName: ""}, fmt.Errorf("invalid number: %s", right)
			}

			return &FcAtom{OptName: left + "." + right}, nil
		}
	}

	return &FcAtom{OptName: left}, nil
}
