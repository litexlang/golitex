package litexparser

import (
	"fmt"
	"strconv"
)

type FcInfixOptPrecedence int

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
	if parser.is(BuiltinSyms["("]) {
		return parser.parseBracedFcExpr()
	}

	// if parser.is(BuiltinSyms["["]) {
	// 	return parser.parseFcLambdaFn()
	// }

	if parser.curTokenBeginWithNumber() {
		return parser.parseNumberStr()
	}

	curFc, err := parser.parseFcStrAndFcFnRetVal()
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	if !parser.is(BuiltinSyms["."]) {
		return curFc, nil
	}

	fcArr := []Fc{curFc}
	for !parser.ExceedEnd() && parser.is(BuiltinSyms["."]) {
		err = parser.skip(BuiltinSyms["."])
		if err != nil {
			return nil, &parserErr{err, parser}
		}

		curFc, err = parser.parseFcStrAndFcFnRetVal()
		if err != nil {
			return nil, &parserErr{err, parser}
		}

		fcArr = append(fcArr, curFc)
	}

	ret := FcMemChain(fcArr)

	return &ret, nil
}

func (parser *Parser) parseBracedFcExpr() (Fc, error) {
	parser.skip(BuiltinSyms["("])
	fc, err := parser.ParseFc()
	if err != nil {
		return nil, &parserErr{err, parser}
	}
	parser.skip(BuiltinSyms[")"])
	return fc, nil
}

func (parser *Parser) parseFcStrAndFcFnRetVal() (Fc, error) {
	// 如果 1 out of range了，那返回值是 “”
	strAtSecondPosition := parser.strAt(1)

	if strAtSecondPosition != BuiltinSyms["["] && strAtSecondPosition != BuiltinSyms["("] {
		return parser.parseFcStr()
	} else {
		return parser.parseFcFnRetVal()
	}
}

func (parser *Parser) parseFcFnRetVal() (Fc, error) {
	var previousFc Fc
	previousFc, err := parser.parseFcStr()
	if err != nil {
		return nil, err
	}

	for !parser.ExceedEnd() && (parser.is(BuiltinSyms["["]) || parser.is(BuiltinSyms["("])) {
		typeParamsPtr := &[]typeVar{}
		if parser.is(BuiltinSyms["["]) {
			typeParamsPtr, err = parser.parseBracketedTypeVarArr()
			if err != nil {
				return nil, &parserErr{err, parser}
			}
		}

		varParamsPtr := &[]Fc{}
		if parser.is(BuiltinSyms["("]) {
			varParamsPtr, err = parser.parseBracedFcArr()
			if err != nil {
				return nil, &parserErr{err, parser}
			}
		}

		previousFc = &FcFnRetValue{previousFc, *typeParamsPtr, *varParamsPtr}
	}

	return previousFc, nil
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
	node, err := parser.parseFcUnaryExpr()
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	// process infix operators recursively
	for {
		curToken, err := parser.currentToken()
		if err != nil {
			return node, nil
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

		node = &FcFnRetValue{
			FcStr(curToken),
			[]typeVar{},
			[]Fc{node, right},
		}
	}

	return node, nil
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
			[]typeVar{},
			[]Fc{right},
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

	if parser.is(BuiltinSyms["."]) {
		parser.skip()
		right, err := parser.next()

		if err != nil {
			return "", err
		}

		_, err = strconv.Atoi(right)
		if err != nil {
			return "", fmt.Errorf("invalid number: %s", right)
		}

		return FcStr(left) + "." + FcStr(right), nil
	}

	return FcStr(left), nil
}

// func (parser *Parser) parseFcLambdaFn() (*FcLambdaFn, error) {

// 	return nil, nil
// }
