package parser

func ParseTopLevelStmt(tokenStmtBlock *TokenStmt) (TopStmt, error) {
	pub := false
	if tokenStmtBlock.Header[0] == Keywords["pub"] {
		tokenStmtBlock.Header = tokenStmtBlock.Header[1:] // remove the leading 'pub'
	}

	stmt, err := ParseStmt(tokenStmtBlock)
	topStmt := stmt.toTopStmt()

	if err != nil {
		return nil, err
	}

	if pub {
		err = (topStmt).setPubTrue()
		if err != nil {
			return nil, err
		}
	}

	return topStmt, nil
}

func ParseStmt(tokenStmtBlock *TokenStmt) (Stmt, error) {
	switch tokenStmtBlock.Header[0] {
	case Keywords["concept"]:
		return parseDefConceptStmt(tokenStmtBlock)
	case Keywords["property"]:
		return parseDefPropertyStmt(tokenStmtBlock)
	case Keywords["fn"]:
		return parseDefFnStmt(tokenStmtBlock)
	default:
		return parseFactStmt(tokenStmtBlock)
	}
}

func parseDefConceptStmt(tokenStmtBlock *TokenStmt) (*DefConceptStmt, error) {
	conceptVar := tokenStmtBlock.Header[1]
	conceptName := tokenStmtBlock.Header[2]

	start := 3

	var conceptParams *[]VarTypePair = nil
	var err error
	if tokenStmtBlock.Header[start] == KeywordSymbols["["] {
		conceptParams, err = parseTypeVarPairBracket(&tokenStmtBlock.Header, &start)
		if err != nil {
			return nil, err
		}
	}

	var varParams *[]VarTypePair = nil
	if tokenStmtBlock.Header[start] == KeywordSymbols["("] {
		varParams, err = parseTypeVarPairBrace(&tokenStmtBlock.Header, &start)
		if err != nil {
			return nil, err
		}
	}

	skip(&tokenStmtBlock.Header, &start, KeywordSymbols[":"])

	var existFacts []ExistStmt = nil
	var facts []FactStmt = nil

	for _, stmt := range tokenStmtBlock.Body {
		if stmt.Header[0] == Keywords["property"] {
			for _, factBlock := range stmt.Body {
				fact, err := parseFactStmt(&factBlock)
				if err != nil {
					return nil, err
				}
				facts = append(facts, fact)
			}
		} else if stmt.Header[0] == Keywords["exist"] {
			for _, factBlock := range stmt.Body {
				fact, err := parseExistFactStmt(&factBlock)
				if err != nil {
					return nil, err
				}
				facts = append(facts, fact)
			}
		} else {
			fact, err := parseFactStmt(&stmt)
			if err != nil {
				return nil, err
			}
			facts = append(facts, fact)
		}
	}

	return &DefConceptStmt{conceptVar, conceptName, conceptParams, nil, varParams, nil, &existFacts, &facts}, nil
}

func parseDefFnStmt(tokenStmtBlock *TokenStmt) (*DefConceptStmt, error) {
	// TODO: Implement parsing logic for concept statement
	return nil, nil
}

func parseDefPropertyStmt(tokenStmtBlock *TokenStmt) (*DefPropertyStmt, error) {
	// TODO: Implement parsing logic for property statement
	return nil, nil
}

func parseFactStmt(tokenStmtBlock *TokenStmt) (FactStmt, error) {
	if tokenStmtBlock.Header[0] == KeywordSymbols["$"] {
		return parseFuncPtyStmt(tokenStmtBlock)
	}
	return nil, nil
}

func parseExistFactStmt(tokenStmt *TokenStmt) (*ExistStmt, error) {
	// TODO: Implement parsing logic for exist fact statement
	return nil, nil
}

func parseFuncPtyStmt(tokenStmt *TokenStmt) (*PtyStmt, error) {
	var start = 0
	skip(&tokenStmt.Header, &start, KeywordSymbols["$"])
	name := tokenStmt.Header[start]
	start++
	params, err := parseBracedVars(&tokenStmt.Header, &start)
	if err != nil {
		return nil, err
	}

	return &PtyStmt{name, params}, nil
}

func parseIfStmt(tokenStmt *TokenStmt) (*IfStmt, error) {
	start := 0
	skip(&tokenStmt.Header, &start, Keywords["if"])

	var conceptParams *[]VarTypePair = nil
	var err error = nil
	if tokenStmt.Header[start] == KeywordSymbols["["] {
		conceptParams, err = parseTypeVarPairBracket(&tokenStmt.Header, &start)
		if err != nil {
			return nil, err
		}
	}

	var varParams *[]VarTypePair = nil
	if tokenStmt.Header[start] == KeywordSymbols["("] {
		varParams, err = parseTypeVarPairBrace(&tokenStmt.Header, &start)
		if err != nil {
			return nil, err
		}
	}

	facts := []FactStmt{}
	for _, stmt := range tokenStmt.Body {
		fact, err := parseFactStmt(&stmt)
		if err != nil {
			return nil, err
		}
		facts = append(facts, fact)
	}

	return &IfStmt{conceptParams, nil, varParams, nil, facts}, nil
}
