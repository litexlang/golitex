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
	typeParams := []FcStr{}
	parser.skip(KeySyms["["])

	for {
		fcStr, err := parser.parseFcStr()

		if err != nil {
			return nil, err
		}

		typeParams = append(typeParams, fcStr)

		if parser.isAndSkip(KeySyms["]"]) {
			break
		}

		if err := parser.testAndSkip(KeySyms[","]); err != nil {
			return nil, err
		}
	}

	return &typeParams, nil
}

func (parser *Parser) parseBracedFcArr() (*[]Fc, error) {
	typeParams := []FcStr{}
	parser.skip(KeySyms["("])

	for {
		fcStr, err := parser.parseFcStr()

		if err != nil {
			return nil, err
		}

		typeParams = append(typeParams, fcStr)

	}

	return &typeParams, nil
}

func (parser *Parser) parseFcStr() (FcStr, error) {
	return nil, nil
}
