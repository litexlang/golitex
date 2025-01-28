package parser

func (parser *Parser) parseFc() (Fc, error) {
	curFc, err := parser.parseFcStrAndFcFnRetVal()
	if err != nil {
		return nil, err
	}

	if !parser.is(BuiltinSyms["."]) {
		return curFc, nil
	}

	fcArr := []Fc{curFc}
	for !parser.isEnd() && parser.is(BuiltinSyms["."]) {
		err = parser.skip(BuiltinSyms["."])
		if err != nil {
			return nil, err
		}

		curFc, err = parser.parseFcStrAndFcFnRetVal()
		if err != nil {
			return nil, err
		}

		fcArr = append(fcArr, curFc)
	}

	ret := FcExpr(fcArr)

	return &ret, nil
}

func (parser *Parser) parseFcStrAndFcFnRetVal() (Fc, error) {
	firstSymbolPtr, err := parser.parseFcStr()
	if err != nil {
		return nil, err
	}

	if !parser.is(BuiltinSyms["["]) && !parser.is(BuiltinSyms["("]) {
		return firstSymbolPtr, nil
	}

	var previousFc Fc = firstSymbolPtr

	for !parser.isEnd() && (parser.is(BuiltinSyms["["]) || parser.is(BuiltinSyms["("])) {
		curFcc := calledFcFnRetValue{previousFc, []FcStr{}, []Fc{}}

		typeParamsPtr := &[]FcStr{}
		if parser.is(BuiltinSyms["["]) {
			typeParamsPtr, err = parser.parseBracketedFcString()
			if err != nil {
				return nil, err
			}
		}

		varParamsPtr := &[]Fc{}
		if parser.is(BuiltinSyms["("]) {
			varParamsPtr, err = parser.parseBracedFcArr()
			if err != nil {
				return nil, err
			}
		}

		curFcc.typeParams = *typeParamsPtr
		curFcc.varParams = *varParamsPtr
		previousFc = &curFcc
	}

	return previousFc, nil
}

func (parser *Parser) parseBracketedFcString() (*[]FcStr, error) {
	params := []FcStr{}
	parser.skip(BuiltinSyms["["])

	for {
		fcStr, err := parser.parseFcStr()

		if err != nil {
			return nil, err
		}

		params = append(params, fcStr)

		if parser.isAndSkip(BuiltinSyms["]"]) {
			break
		}

		if err := parser.testAndSkip(BuiltinSyms[","]); err != nil {
			return nil, err
		}
	}

	return &params, nil
}

func (parser *Parser) parseBracedFcArr() (*[]Fc, error) {
	params := []Fc{}
	parser.skip(BuiltinSyms["("])

	for {
		fc, err := parser.parseFc()

		if err != nil {
			return nil, err
		}

		params = append(params, fc)

		if parser.isAndSkip(BuiltinSyms[")"]) {
			break
		}

		if err := parser.testAndSkip(BuiltinSyms[","]); err != nil {
			return nil, err
		}
	}

	return &params, nil
}

func (parser *Parser) parseFcStr() (FcStr, error) {
	tok, err := parser.next()
	if err != nil {
		return "", err
	}
	return FcStr(tok), nil
}

func (parser *Parser) parseConceptTypeStruct() (typeConcept, error) {
	tok, err := parser.next()
	if err != nil {
		return "", err
	}
	return typeConcept(tok), nil
}

func (parser *Parser) parseTypeVar() (typeVar, error) {
	tok, err := parser.next()
	if err != nil {
		return "", err
	}
	return typeVar(tok), nil
}

func (parser *Parser) parseBracketedVarTypePair() (*[]typeConceptPair, error) {
	pairs := []typeConceptPair{}
	parser.skip(BuiltinSyms["["])

	for {
		varName, err := parser.parseTypeVar()
		if err != nil {
			return nil, err
		}

		typeName, err := parser.parseConceptTypeStruct()
		if err != nil {
			return nil, err
		}

		pairs = append(pairs, typeConceptPair{varName, typeName})

		if parser.isAndSkip(BuiltinSyms["]"]) {
			break
		}

		if err := parser.testAndSkip(BuiltinSyms[","]); err != nil {
			return nil, err
		}
	}

	return &pairs, nil
}

func (parser *Parser) parseFcVarTypePairArrEndWithColon() (*[]fcTypePair, error) {
	pairs := []fcTypePair{}

	for {
		varName, err := parser.parseFcStr()
		if err != nil {
			return nil, err
		}

		typeName, err := parser.parseFcType()
		if err != nil {
			return nil, err
		}

		pairs = append(pairs, fcTypePair{(varName), (typeName)})

		if parser.isAndSkip(BuiltinSyms[":"]) {
			break
		}

		if err := parser.testAndSkip(BuiltinSyms[","]); err != nil {
			return nil, err
		}
	}

	return &pairs, nil
}

func (parser *Parser) parseFcFnType() (*fcFnType, error) {
	parser.skip()

	typeParamsTypes := &[]typeConceptPair{}
	var err error = nil
	if parser.is(BuiltinSyms["["]) {
		typeParamsTypes, err = parser.parseBracketedTypeConceptPairArray()
		if err != nil {
			return nil, err
		}
	}

	varParamsTypes := &[]fcTypePair{}
	if parser.is(BuiltinSyms["("]) {
		varParamsTypes, err = parser.parseBracedFcTypePairArray()
		if err != nil {
			return nil, err
		}

	}

	retType, err := parser.parseFnRetType()
	if err != nil {
		return nil, err
	}

	return &fcFnType{*typeParamsTypes, *varParamsTypes, retType}, nil
}

func (parser *Parser) parseBracketedTypeConceptPairArrAndBracedFcTypePairArr() (*[]typeConceptPair, *[]fcTypePair, error) {
	typeParamsTypes := &[]typeConceptPair{}
	var err error = nil
	if parser.is(BuiltinSyms["["]) {
		typeParamsTypes, err = parser.parseBracketedTypeConceptPairArray()
		if err != nil {
			return nil, nil, err
		}
	}

	varParamsTypes := &[]fcTypePair{}
	if parser.is(BuiltinSyms["("]) {
		varParamsTypes, err = parser.parseBracedFcTypePairArray()
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
		return nil, err
	}

	typeParamsTypes, varParamsTypes, err := parser.parseBracketedTypeConceptPairArrAndBracedFcTypePairArr()
	if err != nil {
		return nil, err
	}

	retType, err := parser.parseFnRetType()
	if err != nil {
		return nil, err
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
		return nil, err
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

func (parser *Parser) parseTypeConcept() (typeConcept, error) {
	tok, err := parser.next()
	if err != nil {
		return "", err
	}
	return typeConcept(tok), nil
}

func (parser *Parser) parseBracketedTypeConceptPairArray() (*[]typeConceptPair, error) {
	concepts := []typeConceptPair{}
	parser.skip(BuiltinSyms["["])

	for {
		name, err := parser.parseTypeVar()
		if err != nil {
			return nil, err
		}

		concept, err := parser.parseTypeConcept()
		if err != nil {
			return nil, err
		}

		concepts = append(concepts, typeConceptPair{name, concept})

		if parser.isAndSkip(BuiltinSyms["]"]) {
			break
		}

		if err := parser.testAndSkip(BuiltinSyms[","]); err != nil {
			return nil, err
		}
	}

	return &concepts, nil
}

func (parser *Parser) parseBracedFcTypePairArray() (*[]fcTypePair, error) {
	pairs := []fcTypePair{}
	parser.skip(BuiltinSyms["("])

	for {
		fcStr, err := parser.parseFcStr()
		if err != nil {
			return nil, err
		}

		fcType, err := parser.parseFcType()
		if err != nil {
			return nil, err
		}

		pairs = append(pairs, fcTypePair{fcStr, fcType})

		if parser.isAndSkip(BuiltinSyms[")"]) {
			break
		}

		if err := parser.testAndSkip(BuiltinSyms[","]); err != nil {
			return nil, err
		}
	}

	return &pairs, nil
}

func (parser *Parser) parseVarDecl() (*fcVarDecl, error) {
	parser.next()
	name, err := parser.next()
	if err != nil {
		return nil, err
	}

	// TODO
	typ, err := parser.parseFcVarType()
	if err != nil {
		return nil, err
	}

	return &fcVarDecl{name, typ}, nil
}

func (parser *Parser) parsePropertyDecl() (*propertyDecl, error) {
	parser.next()
	name, err := parser.next()
	if err != nil {
		return nil, err
	}

	typeParams, varParams, err := parser.parseBracketedTypeConceptPairArrAndBracedFcTypePairArr()
	if err != nil {
		return nil, err
	}

	return &propertyDecl{name, propertyType{*typeParams, *varParams}}, nil
}
