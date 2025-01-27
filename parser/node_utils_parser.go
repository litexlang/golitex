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

	ret := FcMemberAccessExpr(fcArr)

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
		curFcc := FcFnRetVal{previousFc, []FcStr{}, []Fc{}}

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

// func (parser *Parser) parseVarType() (fcType, error) {
// 	if parser.is(Keywords["fn"]) {
// 		return parser.parseFcFnType()
// 	}

// 	tok, err := parser.next()
// 	if err != nil {
// 		return fcVarType(""), err
// 	}
// 	return fcVarType(tok), nil
// }

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

func (parser *Parser) parseBracedForallVarTypePair() (*[]forallVarTypePair, error) {
	pairs := []forallVarTypePair{}
	parser.skip(BuiltinSyms["("])

	for {
		varName, err := parser.parseFcStr()
		if err != nil {
			return nil, err
		}

		typeName, err := parser.parseForallVarType()
		if err != nil {
			return nil, err
		}

		pairs = append(pairs, forallVarTypePair{(varName), (typeName)})

		if parser.isAndSkip(BuiltinSyms[")"]) {
			break
		}

		if err := parser.testAndSkip(BuiltinSyms[","]); err != nil {
			return nil, err
		}
	}

	return &pairs, nil
}

func (parser *Parser) parseForallVarTypePairArrEndWithColon() (*[]forallVarTypePair, error) {
	pairs := []forallVarTypePair{}

	for {
		varName, err := parser.parseFcStr()
		if err != nil {
			return nil, err
		}

		typeName, err := parser.parseForallVarType()
		if err != nil {
			return nil, err
		}

		pairs = append(pairs, forallVarTypePair{(varName), (typeName)})

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
	parser.skip() // 不能是 parser.skip(Keywords["fn"]) 因为parse fnDeclStmt的时候，我skip的其实是函数名

	typeParamsTypes := &[]typeConcept{}
	var err error = nil
	if parser.is(BuiltinSyms["["]) {
		typeParamsTypes, err = parser.parseBracketedTypeConceptArray()
		if err != nil {
			return nil, err
		}
	}

	varParamsTypes, err := parser.parseBracedFcTypeArray()
	if err != nil {
		return nil, err
	}

	retType, err := parser.parseFcType()

	return &fcFnType{*typeParamsTypes, *varParamsTypes, retType}, nil
}

func (parser *Parser) parseForallVarType() (forallVarType, error) {
	if parser.is(Keywords["fn"]) {
		return parser.parseFcFnType()
	} else if parser.is(Keywords["property"]) {
		return parser.parsePropertyType()
	} else {
		return parser.parseFcVarType()
	}
}

func (parser *Parser) parseFcType() (fcType, error) {
	if parser.is(Keywords["fn"]) {
		return parser.parseFcFnType()
	} else {
		return parser.parseFcVarType()
	}
}

func (parser *Parser) parsePropertyType() (*propertyType, error) {
	parser.skip()

	typeParams, err := parser.parseBracketedTypeConceptArray()
	if err != nil {
		return nil, err
	}

	varParams, err := parser.parseBracedForallVarTypeArray()
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

func (parser *Parser) parseBracketedTypeConceptArray() (*[]typeConcept, error) {
	concepts := []typeConcept{}
	parser.skip(BuiltinSyms["["])

	for {
		concept, err := parser.parseTypeConcept()
		if err != nil {
			return nil, err
		}

		concepts = append(concepts, concept)

		if parser.isAndSkip(BuiltinSyms["]"]) {
			break
		}

		if err := parser.testAndSkip(BuiltinSyms[","]); err != nil {
			return nil, err
		}
	}

	return &concepts, nil
}

func (parser *Parser) parseBracedFcTypeArray() (*[]fcType, error) {
	types := []fcType{}
	parser.skip(BuiltinSyms["("])

	for {
		t, err := parser.parseFcType()
		if err != nil {
			return nil, err
		}

		types = append(types, t)

		if parser.isAndSkip(BuiltinSyms[")"]) {
			break
		}

		if err := parser.testAndSkip(BuiltinSyms[","]); err != nil {
			return nil, err
		}
	}

	return &types, nil
}

func (parser *Parser) parseBracedForallVarTypeArray() (*[]forallVarType, error) {
	varTypes := []forallVarType{}
	parser.skip(BuiltinSyms["("])

	for {
		t, err := parser.parseForallVarType()
		if err != nil {
			return nil, err
		}

		varTypes = append(varTypes, t)

		if parser.isAndSkip(BuiltinSyms[")"]) {
			break
		}

		if err := parser.testAndSkip(BuiltinSyms[","]); err != nil {
			return nil, err
		}
	}

	return &varTypes, nil
}
