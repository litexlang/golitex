package litexparser

import (
	"fmt"
	"strconv"
)

func (parser *Parser) parseFcAtom() (Fc, error) {
	if parser.is(KeywordLeftParen) {
		return parser.parseBracedFcExpr()
	}

	if parser.curTokenBeginWithNumber() {
		return parser.parseNumberStr()
	}

	// TODO: 这里需要考虑xxx::yyy这种情况
	fcStr, err := parser.parseFcStr()
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	strAtSecondPosition := parser.strAtCurIndexPlus(0)

	if strAtSecondPosition != KeywordLeftParen {
		return fcStr, nil
	} else {
		return parser.parseFcFnRetVal(fcStr)
	}
}

// func (parser *Parser) parseFcChain(curFc FcChainMem) (*FcChain, error) {
// 	fcArr := []FcChainMem{curFc}
// 	var err error = nil
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

func (parser *Parser) parseFcFnRetVal(optName FcStr) (*FcFnRetValue, error) {
	typeParamsObjParamsPairs, err := parser.parseTypeParamsObjParamsPairs()

	if err != nil {
		return nil, err
	}

	return &FcFnRetValue{optName, *typeParamsObjParamsPairs}, nil
}

func (parser *Parser) parseTypeParamsObjParamsPairs() (*[]ObjParams, error) {
	var err error

	pairs := []ObjParams{}

	for !parser.ExceedEnd() && (parser.is(KeywordLeftParen)) {
		varParamsPtr := &[]Fc{}
		varParamsPtr, err = parser.parseBracedFcArr()
		if err != nil {
			return nil, &parserErr{err, parser}
		}

		pairs = append(pairs, ObjParams{*varParamsPtr})
	}

	return &pairs, nil
}

func (parser *Parser) parseFcStr() (FcStr, error) {
	value, err := parser.next()
	if err != nil {
		return FcStr{Value: ""}, err
	}

	fromPkg := ""
	if parser.is(KeywordColonColon) {
		fromPkg = value
		err := parser.skip(KeywordColonColon)
		if err != nil {
			return FcStr{Value: ""}, err
		}
		value, err = parser.next()
		if err != nil {
			return FcStr{Value: ""}, err
		}
	}

	return FcStr{FromPkg: fromPkg, Value: value}, nil
}

type FcInfixOptPrecedence int

// TODO: implement other operators. How logical operators work is also not implemented
const (
	precLowest         FcInfixOptPrecedence = iota
	precAssignment                          // =
	precOr                                  // or
	precAnd                                 // and
	precEquality                            // == !=
	precComparison                          // < > <= >=
	precAddition                            // + -
	precMultiplication                      // / *
	precUnary                               // - !
	precExponentiation                      // ^
)

var precedenceMap = map[string]FcInfixOptPrecedence{
	"+": precAddition,
	"-": precAddition,
	"*": precMultiplication,
	"/": precMultiplication,
	"^": precExponentiation,
}

// All Unary operators have higher precedence than infix operators
var unaryPrecedence = map[string]FcInfixOptPrecedence{
	"-": precUnary,
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

		left = &FcFnRetValue{
			FcStr{Value: curToken},
			[]ObjParams{{[]Fc{left, right}}},
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
		return &FcFnRetValue{
			FcStr{Value: unaryOp},
			[]ObjParams{{[]Fc{right}}},
		}, nil
	} else {
		return parser.parseFcAtom()
	}

}

func (parser *Parser) parseNumberStr() (FcStr, error) {
	left, err := parser.next()

	if err != nil {
		return FcStr{Value: ""}, err
	}

	if left[0] == '0' {
		return FcStr{Value: ""}, fmt.Errorf("invalid number, 0 is not allowed in the first position of a number")
	}

	_, err = strconv.Atoi(left)
	if err != nil {
		return FcStr{Value: ""}, fmt.Errorf("invalid number: %s", left)
	}

	if parser.is(KeywordDot) {
		// The member after . might be a member or a number
		_, err := strconv.Atoi(parser.strAtCurIndexPlus(1))
		if err != nil {
			return FcStr{Value: left}, nil
		} else {
			parser.skip()
			right, err := parser.next()

			if err != nil {
				return FcStr{Value: ""}, fmt.Errorf("invalid number: %s", right)
			}

			return FcStr{Value: left + "." + right}, nil
		}
	}

	return FcStr{Value: left}, nil
}
