package parser

import "fmt"

func ParseStmt(tokenStmtBlock *TokenStmt) (Stmt, error) {
	switch tokenStmtBlock.Header[0] {
	case Keywords["concept"]:
		return parseConceptStmt(tokenStmtBlock)
	case Keywords["property"]:
		return parsePropertyStmt(tokenStmtBlock)
	case Keywords["fn"]:
		return parseFnStmt(tokenStmtBlock)
	default:
		return nil, fmt.Errorf("Invalid statement: %s", tokenStmtBlock.String())
	}
}

func parseConceptStmt(tokenStmtBlock *TokenStmt) (*DefConceptStmt, error) {
	// TODO: Implement parsing logic for concept statement
	return nil, nil
}

func parseFnStmt(tokenStmtBlock *TokenStmt) (*DefConceptStmt, error) {
	// TODO: Implement parsing logic for concept statement
	return nil, nil
}

func parsePropertyStmt(tokenStmtBlock *TokenStmt) (*DefPropertyStmt, error) {
	// TODO: Implement parsing logic for property statement
	return nil, nil
}
