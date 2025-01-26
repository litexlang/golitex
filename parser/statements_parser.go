package parser

import "fmt"

func (stmt *TokenStmt) ParseTopLevelStmt() (*TopStmt, error) {
	pub := false
	if stmt.Header.is(BuiltinSyms["pub"]) {
		stmt.Header.skip()
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
	if stmt.Header.is(BuiltinSyms["$"]) {
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
	stmt.Header.skip(BuiltinSyms["$"])
	fc, err := stmt.Header.parseFc()
	if err != nil {
		return nil, err
	}
	return &FuncPtyStmt{true, fc}, nil
}

func (stmt *TokenStmt) parseForallStmt() (*ForallStmt, error) {
	stmt.Header.skip(Keywords["forall"])

	typeParams := &[]typeConceptPair{}
	var err error = nil
	if stmt.Header.is(BuiltinSyms["["]) {
		typeParams, err = stmt.Header.parseBracketedVarTypePair()
		if err != nil {
			return nil, err
		}
	}

	varParams, err := stmt.Header.parseVarTypePairArrEndWithColon()
	if err != nil {
		return nil, err
	}

	ifFacts := &[]FactStmt{}
	thenFacts := &[]FactStmt{}

	if len(stmt.Body) > 0 && (stmt.Body)[0].Header.is(Keywords["if"]) {
		ifFacts, err = stmt.Body[0].parseFactsBlock()
		if err != nil {
			return nil, err
		}

		if len(stmt.Body) == 2 && (stmt.Body)[1].Header.is(Keywords["then"]) {
			thenFacts, err = stmt.Body[1].parseFactsBlock()
			if err != nil {
				return nil, err
			}
		} else {
			return nil, fmt.Errorf("expected 'then'")
		}
	} else {
		thenFacts, err = stmt.parseBodyFacts()
		if err != nil {
			return nil, err
		}
	}

	return &ForallStmt{*typeParams, *varParams, *ifFacts, *thenFacts}, nil
}

func (stmt *TokenStmt) parseBodyFacts() (*[]FactStmt, error) {
	if len(stmt.Body) == 0 {
		return &[]FactStmt{}, nil
	}

	facts := &[]FactStmt{}
	for _, f := range stmt.Body {
		fact, err := f.parseFactStmt()
		if err != nil {
			return nil, err
		}
		*facts = append(*facts, fact)
	}

	return facts, nil
}

func (stmt *TokenStmt) parseFactsBlock() (*[]FactStmt, error) {
	ifFacts := &[]FactStmt{}
	stmt.Header.skip()
	if err := stmt.Header.testAndSkip(BuiltinSyms[":"]); err != nil {
		return nil, err
	}

	for _, curStmt := range stmt.Body {
		fact, err := curStmt.parseFactStmt()
		if err != nil {
			return nil, err
		}
		*ifFacts = append(*ifFacts, fact)
	}

	return ifFacts, nil
}

func (stmt *TokenStmt) parseDefPropertyStmt() (*DefPropertyStmt, error) {
	stmt.Header.skip(Keywords["property"])

	name, err := stmt.Header.next()
	if err != nil {
		return nil, err
	}

	typeParams := &[]typeConceptPair{}
	if stmt.Header.is(BuiltinSyms["["]) {
		typeParams, err = stmt.Header.parseBracketedVarTypePair()
		if err != nil {
			return nil, err
		}
	}

	varParams, err := stmt.Header.parseBracedVarTypePair()
	if err != nil {
		return nil, err
	}

	if err := stmt.Header.testAndSkip(BuiltinSyms[":"]); err != nil {
		return nil, err
	}

	ifFacts := &[]FactStmt{}
	thenFacts := &[]FactStmt{}

	if len(stmt.Body) > 0 && (stmt.Body)[0].Header.is(Keywords["if"]) {
		ifFacts, err = stmt.Body[0].parseFactsBlock()
		if err != nil {
			return nil, err
		}

		if len(stmt.Body) == 2 && (stmt.Body)[1].Header.is(Keywords["then"]) {
			thenFacts, err = stmt.Body[1].parseFactsBlock()
			if err != nil {
				return nil, err
			}
		} else {
			return nil, fmt.Errorf("expected 'then'")
		}
	} else {
		thenFacts, err = stmt.parseBodyFacts()
		if err != nil {
			return nil, err
		}
	}

	return &DefPropertyStmt{name, *typeParams, *varParams, *ifFacts, *thenFacts}, nil
}
