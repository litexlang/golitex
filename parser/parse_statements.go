package parser

func (parser Parser) ParseTopLevelStmt(tokenStmtBlock *TokenStmt) (*TopStmt, error) {
	pub := false
	if tokenStmtBlock.Header.is(KeySyms["pub"]) {
		err := tokenStmtBlock.Header.setIndex(1)
		if err != nil {
			return nil, err
		}
		pub = true
	}

	stmt, err := parser.ParseStmt(tokenStmtBlock)
	if err != nil {
		return nil, err
	}

	return &TopStmt{stmt, pub}, nil
}

func (parser Parser) ParseStmt(tokenStmtBlock *TokenStmt) (Stmt, error) {
	cur, err := tokenStmtBlock.Header.currentToken()
	if err != nil {
		return nil, err
	}

	switch cur {
	case Keywords["concept"]:
		return parser.parseDefConceptStmt(tokenStmtBlock)
	case Keywords["property"]:
		return parser.parseDefPropertyStmt(tokenStmtBlock)
	case Keywords["fn"]:
		return parser.parseDefFnStmt(tokenStmtBlock)
	default:
		return parser.parseFactStmt(tokenStmtBlock)
	}
}

func (parser Parser) parseDefConceptStmt(tokenStmtBlock *TokenStmt) (*DefConceptStmt, error) {
	return nil, nil
}

func (parser Parser) parseDefFnStmt(tokenStmtBlock *TokenStmt) (*DefConceptStmt, error) {
	// TODO: Implement parsing logic for concept statement
	return nil, nil
}

func (parser Parser) parseDefPropertyStmt(tokenStmtBlock *TokenStmt) (*DefPropertyStmt, error) {
	// TODO: Implement parsing logic for property statement
	return nil, nil
}

func (parser Parser) parseFactStmt(tokenStmtBlock *TokenStmt) (FactStmt, error) {
	cur, err := tokenStmtBlock.Header.currentToken()
	if err != nil {
		return nil, err
	}

	if cur == KeySyms["$"] {
		return parser.parseFuncPtyStmt(tokenStmtBlock)
	} else if cur == Keywords["if"] {
		return parser.parseIfStmt(tokenStmtBlock)
	}

	return nil, nil
}

func (parser Parser) parseFuncPtyStmt(tokenStmt *TokenStmt) (*PtyStmt, error) {
	return nil, nil
}

func (parser Parser) parseIfStmt(tokenStmt *TokenStmt) (*ForallStmt, error) {
	// TODO
	return nil, nil
}
