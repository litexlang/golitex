package parser

import "fmt"

func ParseStmt(tokenStmtBlock *TokenStmtBlock) (Stmt, error) {
	switch tokenStmtBlock.Header[0] {
	case "concept":
		return parseConceptStmt(tokenStmtBlock)
	case "property":
		return parsePropertyStmt(tokenStmtBlock)
	default:
		return nil, fmt.Errorf("Invalid statement: %s", tokenStmtBlock.String())
	}
}

func parseConceptStmt(tokenStmtBlock *TokenStmtBlock) (*DefConceptStmt, error) {
	// TODO: Implement parsing logic for concept statement
	return nil, nil
}

func parsePropertyStmt(tokenStmtBlock *TokenStmtBlock) (*DefPropertyStmt, error) {
	// TODO: Implement parsing logic for property statement
	return nil, nil
}
