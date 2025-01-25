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

func parseFuncPtyStmt(tokenStmt *TokenStmt) (*PtyStmt, error) {
	start := 0
	var err error

	skip(&tokenStmt.Header, &start, KeywordSymbols["$"])
	name := tokenStmt.Header[start]

	typeParams := &[]string{}
	if tokenStmt.Header[start] == KeywordSymbols["["] {
		typeParams, err = ParseSingletonVarBracket(&tokenStmt.Header, &start)
		if err != nil {
			return nil, err
		}
	}

	start++
	params, err := parseBracedVars(&tokenStmt.Header, &start)
	if err != nil {
		return nil, err
	}

	return &PtyStmt{name, *typeParams, params}, nil
}

func parseIfStmt(tokenStmt *TokenStmt) (*ForallStmt, error) {
	// TODO
	return nil, nil
}
