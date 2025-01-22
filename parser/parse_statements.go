package parser

import "fmt"

func ParseStmt(TokenStmtBlock TokenStmtBlock) (Stmt, error) {
	switch TokenStmtBlock.Header[0] {
	case "concept":
		return ParseConceptStmt(TokenStmtBlock)
	case "property":
		return ParsePropertyStmt(TokenStmtBlock)
	default:
		return nil, fmt.Errorf(`Invalid Statement: %s`, &TokenStmtBlock.Header)
	}
}

func ParseConceptStmt(TokenStmtBlock TokenStmtBlock) (*DefConceptStmt, error) {
	// TODO: Implement parsing logic for concept statement
	return nil, nil
}

func ParsePropertyStmt(TokenStmtBlock TokenStmtBlock) (*DefPropertyStmt, error) {
	// TODO: Implement parsing logic for property statement
	return nil, nil
}
