package parser

import "fmt"

func (stmt *TokenStmt) ParseTopLevelStmt() (*TopStmt, error) {
	pub := false
	if stmt.Header.is(KeySyms["pub"]) {
		err := stmt.Header.setIndex(1)
		if err != nil {
			return nil, err
		}
		pub = true
	}

	ret, err := stmt.ParseStmt()
	if err != nil {
		return nil, err
	}

	return &TopStmt{ret, pub}, nil
}

func (stmt *TokenStmt) ParseStmt() (Stmt, error) {
	cur, err := stmt.Header.currentToken()
	if err != nil {
		return nil, err
	}

	switch cur {
	case Keywords["concept"]:
		return stmt.parseDefConceptStmt()
	case Keywords["property"]:
		return stmt.parseDefPropertyStmt()
	case Keywords["fn"]:
		return stmt.parseDefFnStmt()
	default:
		return stmt.parseFactStmt()
	}
}

func (stmt *TokenStmt) parseDefConceptStmt() (*DefConceptStmt, error) {
	return nil, nil
}

func (stmt *TokenStmt) parseDefFnStmt() (*DefConceptStmt, error) {
	// TODO: Implement parsing logic for concept statement
	return nil, nil
}

func (stmt *TokenStmt) parseDefPropertyStmt() (*DefPropertyStmt, error) {
	// TODO: Implement parsing logic for property statement
	return nil, nil
}

func (stmt *TokenStmt) parseFactStmt() (FactStmt, error) {
	if stmt.Header.is(Keywords["forall"]) {
		return stmt.parseForallStmt()
	}

	if stmt.Header.is(Keywords["not"]) {
		return stmt.parseNotFactStmt()
	}

	return stmt.parsePtyStmt()
}

func (stmt *TokenStmt) parsePtyStmt() (*FuncPtyStmt, error) {
	if stmt.Header.is(Keywords["$"]) {
		return stmt.parseFuncPtyStmt()
	}

	return nil, fmt.Errorf("invalid function")
}

func (stmt *TokenStmt) parseNotFactStmt() (FactStmt, error) {
	stmt.Header.skip(Keywords["not"])
	ret, err := stmt.parsePtyStmt()
	if err != nil {
		return nil, err
	}
	ret.setT(false)
	return ret, nil
}

func (stmt *TokenStmt) parseFuncPtyStmt() (*FuncPtyStmt, error) {
	stmt.Header.skip(KeySyms["$"])
	fc, err := stmt.Header.parseFc()
	if err != nil {
		return nil, err
	}
	return &FuncPtyStmt{true, fc}, nil
}

func (stmt *TokenStmt) parseForallStmt() (*ForallStmt, error) {
	return nil, nil
}
