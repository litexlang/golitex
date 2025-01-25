package parser

func (parser *Parser) parseFc() (Fc, error) {
	firstSymbolPtr, err := parser.parseFcStr()
	if err != nil {
		return nil, err
	}

	if !parser.is(KeySyms["["]) && !parser.is(KeySyms["("]) {
		return firstSymbolPtr, nil
	}

	var previousFc Fc = firstSymbolPtr

	for !parser.isEnd() && (parser.is(KeySyms["["]) || parser.is(KeySyms["("])) {
		curFcc := FcFnRetVal{previousFc, []FcStr{}, []Fc{}}

		var typeParamsPtr *[]FcStr
		if parser.is(KeySyms["["]) {
			typeParamsPtr, err = parser.parseBracketedFcString()
			if err != nil {
				return nil, err
			}
		}

		var varParamsPtr *[]Fc
		if parser.is(KeySyms["("]) {
			varParamsPtr, err = parser.parseBracedFcArr()
			if err != nil {
				return nil, err
			}
		}

		curFcc.typeParams = *typeParamsPtr
		curFcc.varParams = *varParamsPtr
		previousFc = curFcc
	}

	return firstSymbolPtr, nil
}

func (parser *Parser) parseBracketedFcString() (*[]FcStr, error) {
	params := []FcStr{}
	parser.skip(KeySyms["["])

	for {
		fcStr, err := parser.parseFcStr()

		if err != nil {
			return nil, err
		}

		params = append(params, fcStr)

		if parser.isAndSkip(KeySyms["]"]) {
			break
		}

		if err := parser.testAndSkip(KeySyms[","]); err != nil {
			return nil, err
		}
	}

	return &params, nil
}

func (parser *Parser) parseBracedFcArr() (*[]Fc, error) {
	params := []Fc{}
	parser.skip(KeySyms["("])

	for {
		fc, err := parser.parseFc()

		if err != nil {
			return nil, err
		}

		params = append(params, fc)

		if parser.isAndSkip(KeySyms[")"]) {
			break
		}

		if err := parser.testAndSkip(KeySyms[","]); err != nil {
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
