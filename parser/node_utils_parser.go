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

func (parser *Parser) parseBracketedVarTypePair() (*[]typeConceptPair, error) {
	pairs := []typeConceptPair{}
	parser.skip(BuiltinSyms["["])

	for {
		varName, err := parser.parseFcStr()
		if err != nil {
			return nil, err
		}

		typeName, err := parser.parseFcStr()
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

func (parser *Parser) parseBracedVarTypePair() (*[]varTypePair, error) {
	pairs := []varTypePair{}
	parser.skip(BuiltinSyms["("])

	for {
		varName, err := parser.parseFcStr()
		if err != nil {
			return nil, err
		}

		typeName, err := parser.parseFcStr()
		if err != nil {
			return nil, err
		}

		pairs = append(pairs, varTypePair{(varName), (typeName)})

		if parser.isAndSkip(BuiltinSyms[")"]) {
			break
		}

		if err := parser.testAndSkip(BuiltinSyms[","]); err != nil {
			return nil, err
		}
	}

	return &pairs, nil
}

func (parser *Parser) parseVarTypePairArrEndWithColon() (*[]varTypePair, error) {
	pairs := []varTypePair{}

	for {
		varName, err := parser.parseFc()
		if err != nil {
			return nil, err
		}

		typeName, err := parser.parseFcStr()
		if err != nil {
			return nil, err
		}

		pairs = append(pairs, varTypePair{(varName), (typeName)})

		if parser.isAndSkip(BuiltinSyms[":"]) {
			break
		}

		if err := parser.testAndSkip(BuiltinSyms[","]); err != nil {
			return nil, err
		}
	}

	return &pairs, nil
}
