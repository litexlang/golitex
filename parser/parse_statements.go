package parser

func ParseTopLevelStmt(tokenStmtBlock *TokenStmt) (TopStmt, error) {
	pub := false
	if tokenStmtBlock.Header[0] == Keywords["pub"] {
		tokenStmtBlock.Header = tokenStmtBlock.Header[1:] // remove the leading 'pub'
	}

	stmt, err := ParseStmt(tokenStmtBlock)

	if err != nil {
		return nil, err
	}

	if pub {
		err = (stmt).setPubTrue()
		if err != nil {
			return nil, err
		}
	}

	return stmt, nil
}

func ParseStmt(tokenStmtBlock *TokenStmt) (TopStmt, error) {
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

func parseConceptStmt(tokenStmtBlock *TokenStmt) (*DefConceptTopStmt, error) {
	// TODO: Implement parsing logic for concept statement
	return nil, nil
}

func parseFnStmt(tokenStmtBlock *TokenStmt) (*DefConceptTopStmt, error) {
	// TODO: Implement parsing logic for concept statement
	return nil, nil
}

func parsePropertyStmt(tokenStmtBlock *TokenStmt) (*DefPropertyTopStmt, error) {
	// TODO: Implement parsing logic for property statement
	return nil, nil
}

func parseOptStmt(tokenStmtBlock *TokenStmt) (*CalledPropertyTopStmt, error) {
	return nil, nil
}

func parseVar(tokenStmtBlock *TokenStmt) (*Var, error) {
	// TODO: Implement parsing logic for symbol
	return nil, nil
}
