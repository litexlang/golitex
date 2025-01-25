package parser

type Parser struct {
	err error
}

func (parser Parser) Err() error {
	return parser.err
}

var LitexParser = Parser{err: nil}

func (parser Parser) ParseTopLevelStmt(tokenStmtBlock *TokenStmt) *TopStmt {
	pub := false
	if tokenStmtBlock.Header[0] == Keywords["pub"] {
		tokenStmtBlock.Header = tokenStmtBlock.Header[1:] // remove the leading 'pub'
		pub = true
	}

	stmt := parser.ParseStmt(tokenStmtBlock)

	if parser.Err() != nil {
		return nil
	}
	return &TopStmt{stmt, pub}
}

func (parser Parser) ParseStmt(tokenStmtBlock *TokenStmt) Stmt {
	switch tokenStmtBlock.Header[0] {
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

func (parser Parser) parseDefConceptStmt(tokenStmtBlock *TokenStmt) *DefConceptStmt {
	return nil
}

func (parser Parser) parseDefFnStmt(tokenStmtBlock *TokenStmt) *DefConceptStmt {
	// TODO: Implement parsing logic for concept statement
	return nil
}

func (parser Parser) parseDefPropertyStmt(tokenStmtBlock *TokenStmt) *DefPropertyStmt {
	// TODO: Implement parsing logic for property statement
	return nil
}

func (parser Parser) parseFactStmt(tokenStmtBlock *TokenStmt) FactStmt {
	if tokenStmtBlock.Header[0] == KeywordSymbols["$"] {
		return LitexParser.parseFuncPtyStmt(tokenStmtBlock)
	} else if tokenStmtBlock.Header[0] == Keywords["if"] {
		return LitexParser.parseIfStmt(tokenStmtBlock)
	}

	return nil
}

func (parser Parser) parseFuncPtyStmt(tokenStmt *TokenStmt) *PtyStmt {
	start := 0
	var err error

	skip(&tokenStmt.Header, &start, KeywordSymbols["$"])
	name := tokenStmt.Header[start]

	typeParams := &[]string{}
	if tokenStmt.Header[start] == KeywordSymbols["["] {
		typeParams, err = ParseSingletonVarBracket(&tokenStmt.Header, &start)
		if err != nil {
			return nil
		}
	}

	start++
	params, err := parseBracedVars(&tokenStmt.Header, &start)
	if err != nil {
		return nil
	}

	return &PtyStmt{name, *typeParams, params}
}

func (parser Parser) parseIfStmt(tokenStmt *TokenStmt) *ForallStmt {
	// TODO
	return nil
}
