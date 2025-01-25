package parser

func ParseTopLevelStmt(tokenStmtBlock *TokenStmt) (*TopStmt, error) {
	pub := false
	if tokenStmtBlock.Header[0] == Keywords["pub"] {
		tokenStmtBlock.Header = tokenStmtBlock.Header[1:] // remove the leading 'pub'
		pub = true
	}

	stmt, err := ParseStmt(tokenStmtBlock)
	if err != nil {
		return nil, err
	}

	topStmt := &TopStmt{stmt, pub}

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
	return nil, nil
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
	} else if tokenStmtBlock.Header[0] == Keywords["if"] {
		return parseIfStmt(tokenStmtBlock)
	}

	return nil, nil
}

func parseExistFactStmt(tokenStmt *TokenStmt) (*ExistStmt, error) {
	// TODO: Implement parsing logic for exist fact statement
	return nil, nil
}

func parseFuncPtyStmt(tokenStmt *TokenStmt) (*PtyStmt, error) {
	start := 0
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

	conceptParams := []VarTypePair{}
	conceptFacts := []FactExprStmt{}
	if tokenStmt.Header[start] == KeywordSymbols["["] {
		bracket, err := parseTypeVarPairBracket(&tokenStmt.Header, &start)
		if err != nil {
			return nil, err
		}
		conceptParams = bracket.pairs
		conceptFacts = bracket.facts
	}

	varParams := []VarTypePair{}
	varFacts := []FactExprStmt{}
	if tokenStmt.Header[start] == KeywordSymbols["("] {
		bracket, err := parseTypeVarPairBrace(&tokenStmt.Header, &start)
		if err != nil {
			return nil, err
		}
		varParams = bracket.pairs
		varFacts = bracket.facts
	}

	facts := []FactStmt{}
	if tokenStmt.Body != nil {
		for _, stmt := range *tokenStmt.Body {
			fact, err := parseFactStmt(&stmt)
			if err != nil {
				return nil, err
			}
			facts = append(facts, fact)
		}
	}

	return &IfStmt{conceptParams, conceptFacts, varParams, varFacts, facts}, nil
}
