package parser

import (
	"fmt"
	"strconv"
)

func (parser *Parser) parseFcAtom() (Fc, error) {
	if parser.is(BuiltinSyms["("]) {
		return parser.parseBracedFcExpr()
	}

	if parser.is(Keywords["as"]) {
		return parser.parseTypedFcWithPrefixAs()
	}

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
	for !parser.isEnd() && parser.is(BuiltinSyms["."]) {
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

	ret := FcExpr(fcArr)

	return &ret, nil
}

func (parser *Parser) parseTypedFcWithPrefixAs() (*typedFc, error) {
	err := parser.skip(Keywords["as"])
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	err = parser.skip(BuiltinSyms["("])
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	fc, err := parser.parseFcExpr()
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	err = parser.skip(BuiltinSyms[","])
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	fcType, err := parser.parseFcType()
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	err = parser.skip(BuiltinSyms[")"])
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	return &typedFc{fc, fcType}, nil
}

func (parser *Parser) parseBracedFcExpr() (Fc, error) {
	parser.skip(BuiltinSyms["("])
	fc, err := parser.parseFcExpr()
	if err != nil {
		return nil, &parserErr{err, parser}
	}
	parser.skip(BuiltinSyms[")"])
	return fc, nil
}

func (parser *Parser) parseFcStrAndFcFnRetVal() (Fc, error) {
	strAtSecondPosition, err := parser.atIndex(1)

	if err != nil {
		return nil, err
	}

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

	for !parser.isEnd() && (parser.is(BuiltinSyms["["]) || parser.is(BuiltinSyms["("])) {
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

		previousFc = &calledFcFnRetValue{previousFc, *typeParamsPtr, *varParamsPtr}
	}

	return previousFc, nil
}

func (parser *Parser) parseBracedFcArr() (*[]Fc, error) {
	params := []Fc{}
	parser.skip(BuiltinSyms["("])

	for {
		fc, err := parser.parseFcAtom()

		if err != nil {
			return nil, &parserErr{err, parser}
		}

		params = append(params, fc)

		if parser.isAndSkip(BuiltinSyms[")"]) {
			break
		}

		if err := parser.testAndSkip(BuiltinSyms[","]); err != nil {
			return nil, &parserErr{err, parser}
		}
	}

	return &params, nil
}

func (parser *Parser) parseBracedFcTypeArr() (*[]fcTypePair, error) {
	ret := []fcTypePair{}
	parser.skip(BuiltinSyms["("])

	for {
		fc, err := parser.parseFcExpr()

		if err != nil {
			return nil, &parserErr{err, parser}
		}

		tp, err := parser.parseFcType()
		if err != nil {
			return nil, &parserErr{err, parser}
		}

		ret = append(ret, fcTypePair{fc, tp})

		if parser.isAndSkip(BuiltinSyms[")"]) {
			break
		}

		if err := parser.testAndSkip(BuiltinSyms[","]); err != nil {
			return nil, &parserErr{err, parser}
		}
	}

	return &ret, nil
}

func (parser *Parser) parseFcStr() (FcStr, error) {

	tok, err := parser.next()
	if err != nil {
		return "", err
	}
	return FcStr(tok), nil
}

func (parser *Parser) parseFcVarTypePairArrEndWithColon() (*[]fcStrTypePair, error) {
	pairs := []fcStrTypePair{}

	for {
		varName, err := parser.parseFcStr()
		if err != nil {
			return nil, &parserErr{err, parser}
		}

		typeName, err := parser.parseFcType()
		if err != nil {
			return nil, &parserErr{err, parser}
		}

		pairs = append(pairs, fcStrTypePair{(varName), (typeName)})

		if parser.isAndSkip(BuiltinSyms[":"]) {
			break
		}

		if err := parser.testAndSkip(BuiltinSyms[","]); err != nil {
			return nil, &parserErr{err, parser}
		}
	}

	return &pairs, nil
}

func (parser *Parser) parseFcFnType() (*fcFnType, error) {
	parser.skip(Keywords["fn"])

	typeParamsTypes := &[]typeConceptPair{}
	var err error = nil
	if parser.is(BuiltinSyms["["]) {
		typeParamsTypes, err = parser.parseBracketedTypeConceptPairArray()
		if err != nil {
			return nil, &parserErr{err, parser}
		}
	}

	varParamsTypes := &[]fcStrTypePair{}
	if parser.is(BuiltinSyms["("]) {
		varParamsTypes, err = parser.parseBracedFcStrTypePairArray()
		if err != nil {
			return nil, &parserErr{err, parser}
		}

	}

	retType, err := parser.parseFnRetType()
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	return &fcFnType{*typeParamsTypes, *varParamsTypes, retType}, nil
}

func (parser *Parser) parseBracketedTypeConceptPairArrAndBracedFcTypePairArr() (*[]typeConceptPair, *[]fcStrTypePair, error) {
	typeParamsTypes := &[]typeConceptPair{}
	var err error = nil
	if parser.is(BuiltinSyms["["]) {
		typeParamsTypes, err = parser.parseBracketedTypeConceptPairArray()
		if err != nil {
			return nil, nil, err
		}
	}

	varParamsTypes := &[]fcStrTypePair{}
	if parser.is(BuiltinSyms["("]) {
		varParamsTypes, err = parser.parseBracedFcStrTypePairArray()
		if err != nil {
			return nil, nil, err
		}
	}

	return typeParamsTypes, varParamsTypes, nil
}

func (parser *Parser) parseFcFnDecl() (*fcFnDecl, error) {
	parser.skip()

	name, err := parser.next()
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	typeParamsTypes, varParamsTypes, err := parser.parseBracketedTypeConceptPairArrAndBracedFcTypePairArr()
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	retType, err := parser.parseFnRetType()
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	return &fcFnDecl{name, fcFnType{*typeParamsTypes, *varParamsTypes, retType}}, nil
}

func (parser *Parser) parseFcType() (fcType, error) {
	if parser.is(Keywords["fn"]) {
		return parser.parseFcFnType()
	} else if parser.is(Keywords["property"]) {
		return parser.parsePropertyType()
	} else {
		return parser.parseFcVarType()
	}
}

func (parser *Parser) parseFnRetType() (fnRetType, error) {
	if parser.is(Keywords["fn"]) {
		return parser.parseFcFnType()
	} else {
		return parser.parseFcVarType()
	}
}

func (parser *Parser) parsePropertyType() (*propertyType, error) {
	parser.skip()

	typeParams, varParams, err := parser.parseBracketedTypeConceptPairArrAndBracedFcTypePairArr()
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	return &propertyType{*typeParams, *varParams}, nil
}

func (parser *Parser) parseFcVarType() (fcVarType, error) {
	v, err := parser.next()
	if err != nil {
		return fcVarType(""), err
	}
	return fcVarType(v), nil
}

func (parser *Parser) parseTypeConcept() (typeConceptStr, error) {
	tok, err := parser.next()
	if err != nil {
		return "", err
	}
	return typeConceptStr(tok), nil
}

func (parser *Parser) parseBracketedTypeConceptPairArray() (*[]typeConceptPair, error) {
	concepts := []typeConceptPair{}
	parser.skip(BuiltinSyms["["])

	for {
		name, err := parser.parseTypeVarStr()
		if err != nil {
			return nil, &parserErr{err, parser}
		}

		concept, err := parser.parseTypeConcept()
		if err != nil {
			return nil, &parserErr{err, parser}
		}

		concepts = append(concepts, typeConceptPair{name, concept})

		if parser.isAndSkip(BuiltinSyms["]"]) {
			break
		}

		if err := parser.testAndSkip(BuiltinSyms[","]); err != nil {
			return nil, &parserErr{err, parser}
		}
	}

	return &concepts, nil
}

func (parser *Parser) parseBracedFcStrTypePairArray() (*[]fcStrTypePair, error) {
	pairs := []fcStrTypePair{}
	parser.skip(BuiltinSyms["("])

	for {
		fcStr, err := parser.parseFcStr()
		if err != nil {
			return nil, &parserErr{err, parser}
		}

		fcType, err := parser.parseFcType()
		if err != nil {
			return nil, &parserErr{err, parser}
		}

		pairs = append(pairs, fcStrTypePair{fcStr, fcType})

		if parser.isAndSkip(BuiltinSyms[")"]) {
			break
		}

		if err := parser.testAndSkip(BuiltinSyms[","]); err != nil {
			return nil, &parserErr{err, parser}
		}
	}

	return &pairs, nil
}

func (parser *Parser) parseVarDecl() (*fcVarDecl, error) {
	parser.skip(Keywords["var"])

	pairs := []fcStrTypePair{}

	name, err := parser.next()
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	typ, err := parser.parseFcVarType()
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	pairs = append(pairs, fcStrTypePair{FcStr(name), typ})

	for parser.is(BuiltinSyms[","]) {
		parser.skip(BuiltinSyms[","])

		name, err := parser.next()
		if err != nil {
			return nil, &parserErr{err, parser}
		}

		typ, err := parser.parseFcVarType()
		if err != nil {
			return nil, &parserErr{err, parser}
		}

		pairs = append(pairs, fcStrTypePair{FcStr(name), typ})

	}

	return &fcVarDecl{pairs}, nil
}

func (parser *Parser) parsePropertyDecl() (*propertyDecl, error) {
	parser.skip(Keywords["property"])
	name, err := parser.next()
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	typeParams, varParams, err := parser.parseBracketedTypeConceptPairArrAndBracedFcTypePairArr()
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	return &propertyDecl{name, propertyType{*typeParams, *varParams}}, nil
}

func (parser *Parser) parseExistDecl() (*propertyDecl, error) {
	parser.skip(Keywords["exist"])
	name, err := parser.next()
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	typeParams, varParams, err := parser.parseBracketedTypeConceptPairArrAndBracedFcTypePairArr()
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	return &propertyDecl{name, propertyType{*typeParams, *varParams}}, nil
}

func (parser *Parser) parseStringArr() (*[]string, error) {
	members := &[]string{}

	for {
		member, err := parser.next()
		if err != nil {
			return nil, &parserErr{err, parser}
		}
		*members = append(*members, member)
		if !parser.is(BuiltinSyms[","]) {
			break
		}
		parser.skip()
	}

	return members, nil
}

func (parser *Parser) parseFcExpr() (Fc, error) {
	return parser.parseAddition()
}

func (parser *Parser) parseAddition() (Fc, error) {
	node, err := parser.parseMultiplication()
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	for {
		if parser.is(BuiltinSyms["+"]) || parser.is(BuiltinSyms["-"]) {
			cur, _ := parser.next()

			right, err := parser.parseMultiplication()
			if err != nil {
				return nil, &parserErr{err, parser}
			}
			node = &calledFcFnRetValue{
				FcStr(cur),
				[]typeVar{},
				[]Fc{node, right},
			}
		} else {
			break
		}
	}

	return node, nil
}

func (parser *Parser) parseMultiplication() (Fc, error) {
	node, err := parser.parseUnary()
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	for {
		if parser.is(BuiltinSyms["*"]) || parser.is(BuiltinSyms["/"]) {
			cur, _ := parser.next()

			right, err := parser.parseUnary()
			if err != nil {
				return nil, &parserErr{err, parser}
			}
			node = &calledFcFnRetValue{
				FcStr(cur),
				[]typeVar{},
				[]Fc{node, right},
			}
		} else {
			break
		}
	}

	return node, nil
}

func (parser *Parser) parseUnary() (Fc, error) {
	if parser.is(BuiltinSyms["-"]) {
		cur, _ := parser.next()

		right, err := parser.parseExponentiation()
		if err != nil {
			return nil, &parserErr{err, parser}
		}
		return &calledFcFnRetValue{
			FcStr(cur),
			[]typeVar{},
			[]Fc{right},
		}, nil
	}

	return parser.parseExponentiation()
}

func (parser *Parser) parseExponentiation() (Fc, error) {
	node, err := parser.parseFcAtom()
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	if parser.is(BuiltinSyms["^"]) {
		cur, _ := parser.next()
		right, err := parser.parseExponentiation()
		if err != nil {
			return nil, &parserErr{err, parser}
		}
		node = &calledFcFnRetValue{
			FcStr(cur),
			[]typeVar{},
			[]Fc{right},
		}
	}

	return node, nil
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

func (parser *Parser) parseIsExpr(left Fc) (*funcPtyStmt, error) {
	opt, err := parser.next()

	if err != nil {
		return nil, &parserErr{err, parser}
	}

	typeParams := &[]typeVar{}
	if parser.is(BuiltinSyms["["]) {
		typeParams, err = parser.parseBracketedTypeVarArr()
		if err != nil {
			return nil, &parserErr{err, parser}
		}

		if len(*typeParams) != 1 {
			return nil, &parserErr{fmt.Errorf("expect one type parameter"), parser}
		}
	}

	fc := &calledFcFnRetValue{FcStr(opt), *typeParams, []Fc{left}}
	return &funcPtyStmt{true, fc}, nil
}

func (parser *Parser) parseTypeVar() (typeVar, error) {
	if parser.is(Keywords["as"]) {
		return parser.parseTypedTypeVar()
	} else {
		return parser.parseTypeVarStr()
	}
}

func (parser *Parser) parseTypedTypeVar() (*typedTypeVar, error) {
	parser.skip(Keywords["as"])
	parser.skip(BuiltinSyms["("])
	value, err := parser.parseTypeVarStr()

	if err != nil {
		return nil, &parserErr{err, parser}
	}

	parser.skip(BuiltinSyms[","])
	concept, err := parser.parseTypeConcept()

	if err != nil {
		return nil, &parserErr{err, parser}
	}

	parser.skip(BuiltinSyms[")"])

	return &typedTypeVar{value, concept}, nil
}

func (parser *Parser) parseTypeVarStr() (typeVarStr, error) {
	name, err := parser.next()
	if err != nil {
		return "", &parserErr{err, parser}
	}

	return typeVarStr(name), nil
}

func (parser *Parser) parseBracketedTypeVarArr() (*[]typeVar, error) {
	arr := &[]typeVar{}

	parser.skip(BuiltinSyms["["])

	for {
		tv, err := parser.parseTypeVar()
		if err != nil {
			return nil, &parserErr{err, parser}
		}
		*arr = append(*arr, tv)

		if parser.is(BuiltinSyms[","]) {
			parser.skip()
			continue
		}

		if !parser.is(BuiltinSyms["]"]) {
			return nil, &parserErr{fmt.Errorf("expect ',' or ']'"), parser}
		} else {
			break
		}
	}

	return arr, nil
}
