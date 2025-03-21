package litexparser

import (
	"fmt"
	"strconv"
)

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

func (parser *Parser) parseFcAtom() (Fc, error) {
	if parser.is(KeywordLeftParen) {
		return parser.parseBracedFcExpr()
	}

	var curFc FcChainMem
	var err error

	if parser.curTokenBeginWithNumber() {
		curFc, err = parser.parseNumberStr()
		if err != nil {
			return nil, &parserErr{err, parser}
		}
	} else {
		curFc, err = parser.parseFcChainMem()
		if err != nil {
			return nil, &parserErr{err, parser}
		}
	}

	if !parser.is(KeywordDot) {
		return curFc, nil
	}

	return parser.parseFcChain(curFc)
}

func (parser *Parser) parseFcChain(curFc FcChainMem) (*FcChain, error) {
	fcArr := []FcChainMem{curFc}
	var err error = nil
	for !parser.ExceedEnd() && parser.is(KeywordDot) {
		err = parser.skip(KeywordDot)
		if err != nil {
			return nil, &parserErr{err, parser}
		}

		curFc, err = parser.parseFcChainMem()
		if err != nil {
			return nil, &parserErr{err, parser}
		}

		fcArr = append(fcArr, curFc)
	}

	ret := FcChain{fcArr}
	return &ret, nil
}

func (parser *Parser) parseBracedFcExpr() (Fc, error) {
	parser.skip(KeywordLeftParen)
	fc, err := parser.ParseFc()
	if err != nil {
		return nil, &parserErr{err, parser}
	}
	parser.skip(KeywordRightParen)
	return fc, nil
}

func (parser *Parser) parseFcChainMem() (FcChainMem, error) {
	// 如果 1 out of range了，那返回值是 “”
	strAtSecondPosition := parser.strAtCurIndexPlus(1)

	if strAtSecondPosition != KeywordLeftParen {
		return parser.parseFcStr()
	} else {
		return parser.parseFcFnRetVal()
	}
}

func (parser *Parser) parseFcFnRetVal() (*FcFnRetValue, error) {
	optName, err := parser.parseFcStr()
	if err != nil {
		return nil, err
	}

	typeParamsObjParamsPairs, err := parser.parseTypeParamsObjParamsPairs()

	if err != nil {
		return nil, err
	}

	return &FcFnRetValue{optName, *typeParamsObjParamsPairs}, nil
}

func (parser *Parser) parseTypeParamsObjParamsPairs() (*[]TypeParamsAndObjParamsPair, error) {
	var err error

	pairs := []TypeParamsAndObjParamsPair{}

	for !parser.ExceedEnd() && (parser.is(KeywordLeftParen)) {
		varParamsPtr := &[]Fc{}
		varParamsPtr, err = parser.parseBracedFcArr()
		if err != nil {
			return nil, &parserErr{err, parser}
		}

		pairs = append(pairs, TypeParamsAndObjParamsPair{*varParamsPtr})
	}

	return &pairs, nil
}

func (parser *Parser) parseFcStr() (FcStr, error) {

	tok, err := parser.next()
	if err != nil {
		return "", err
	}
	return FcStr(tok), nil
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
			FcStr(curToken),
			[]TypeParamsAndObjParamsPair{{[]Fc{left, right}}},
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
			FcStr(unaryOp),
			[]TypeParamsAndObjParamsPair{{[]Fc{right}}},
		}, nil
	} else {
		return parser.parseFcAtom()
	}

}

func (parser *Parser) parseNumberStr() (FcStr, error) {
	left, err := parser.next()

	if err != nil {
		return "", err
	}

	if left[0] == '0' {
		return "", fmt.Errorf("invalid number, 0 is not allowed in the first position of a number")
	}

	_, err = strconv.Atoi(left)
	if err != nil {
		return "", fmt.Errorf("invalid number: %s", left)
	}

	if parser.is(KeywordDot) {
		// The member after . might be a member or a number
		_, err := strconv.Atoi(parser.strAtCurIndexPlus(1))
		if err != nil {
			return FcStr(left), nil
		} else {
			parser.skip()
			right, err := parser.next()

			if err != nil {
				return "", fmt.Errorf("invalid number: %s", right)
			}

			return FcStr(left) + "." + FcStr(right), nil
		}
	}

	return FcStr(left), nil
}
