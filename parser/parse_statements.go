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
		return parseConceptStmt(tokenStmtBlock)
	case Keywords["property"]:
		return parsePropertyStmt(tokenStmtBlock)
	case Keywords["fn"]:
		return parseFnStmt(tokenStmtBlock)
	default:
		return parseOptStmt(tokenStmtBlock)
	}
}

func parseConceptStmt(tokenStmtBlock *TokenStmt) (*DefConceptStmt, error) {
	conceptVar := tokenStmtBlock.Header[1]
	conceptName := tokenStmtBlock.Header[2]

	start := 3

	var conceptParams *[]VarTypePair = nil
	var err error
	if tokenStmtBlock.Header[start] == KeywordChars["["] {
		conceptParams, err = parseTypeVarPairBracket(&tokenStmtBlock.Header, &start)
		if err != nil {
			return nil, err
		}
	}

	var varParams *[]VarTypePair = nil
	if tokenStmtBlock.Header[start] == KeywordChars["("] {
		varParams, err = parseTypeVarPairBrace(&tokenStmtBlock.Header, &start)
		if err != nil {
			return nil, err
		}
	}

	skip(&tokenStmtBlock.Header, &start, KeywordChars[":"])

	var existFacts []ExistFactStmt = nil
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

func parseFnStmt(tokenStmtBlock *TokenStmt) (*DefConceptStmt, error) {
	// TODO: Implement parsing logic for concept statement
	return nil, nil
}

func parsePropertyStmt(tokenStmtBlock *TokenStmt) (*DefPropertyStmt, error) {
	// TODO: Implement parsing logic for property statement
	return nil, nil
}

func parseOptStmt(tokenStmtBlock *TokenStmt) (*CalledPropertyTopStmt, error) {
	return nil, nil
}

func parseFactStmt(tokenStmtBlock *TokenStmt) (*FactStmt, error) {
	// TODO: Implement parsing logic for fact statement
	return nil, nil
}

func parseExistFactStmt(tokenStmt *TokenStmt) (*ExistFactStmt, *Error) {
	// TODO: Implement parsing logic for exist fact statement
	return nil, nil
}
