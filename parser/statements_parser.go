package parser

import "fmt"

func (stmt *tokenBlock) ParseTopLevelStmt() (*TopStmt, error) {
	pub := false
	if stmt.header.is(BuiltinSyms["pub"]) {
		stmt.header.skip()
		pub = true
	}

	ret, err := stmt.ParseStmt()
	if err != nil {
		return nil, err
	}

	return &TopStmt{ret, pub}, nil
}

func (stmt *tokenBlock) ParseStmt() (Stmt, error) {
	cur, err := stmt.header.currentToken()
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
	case Keywords["local"]:
		return stmt.parseLocalStmt()
	default:
		return stmt.parseFactStmt()
	}
}

func (stmt *tokenBlock) parseDefConceptStmt() (*DefConceptStmt, error) {
	stmt.header.skip()

	conceptVar, err := stmt.header.next()
	if err != nil {
		return nil, err
	}

	conceptName, err := stmt.header.next()
	if err != nil {
		return nil, err
	}

	if err := stmt.header.testAndSkip(BuiltinSyms[":"]); err != nil {
		return nil, err
	}

	inherit := &[]typeConcept{}
	typeVarMember := &[]fcVarDecl{}
	typeFnMember := &[]fcFnDecl{}
	typePropertyMember := &[]propertyDecl{}
	varMember := &[]fcVarDecl{}
	fnMember := &[]fcFnDecl{}
	propertyMember := &[]propertyDecl{}
	thenFacts := &[]FactStmt{}

	for _, curStmt := range stmt.body {
		if curStmt.header.is(Keywords["inherit"]) {
			inherit, err = curStmt.parseInherit()
			if err != nil {
				return nil, err
			}
		} else if curStmt.header.is(Keywords["type_member"]) {
			typeVarMember, typeFnMember, typePropertyMember, err = curStmt.parseMember()
			if err != nil {
				return nil, err
			}
		} else if curStmt.header.is(Keywords["var_member"]) {
			varMember, fnMember, propertyMember, err = curStmt.parseMember()
			if err != nil {
				return nil, err
			}
		} else if curStmt.header.is(Keywords["then"]) {
			thenFacts, err = curStmt.parseThenFacts()
			if err != nil {
				return nil, err
			}
		}
	}

	return &DefConceptStmt{typeVar(conceptVar), typeConcept(conceptName), *inherit, *typeVarMember, *typeFnMember, *typePropertyMember, *varMember, *fnMember, *propertyMember, *thenFacts}, nil

}

func (stmt *tokenBlock) parseDefFnStmt() (*DefConceptStmt, error) {
	// TODO: Implement parsing logic for concept statement
	return nil, nil
}

func (stmt *tokenBlock) parseFactStmt() (FactStmt, error) {
	if stmt.header.is(Keywords["forall"]) {
		return stmt.parseForallStmt()
	}

	if stmt.header.is(Keywords["not"]) {
		return stmt.parseNotFactStmt()
	}

	return stmt.parsePtyStmt()
}

func (stmt *tokenBlock) parsePtyStmt() (*FuncPtyStmt, error) {
	if stmt.header.is(BuiltinSyms["$"]) {
		return stmt.parseFuncPtyStmt()
	}

	return nil, fmt.Errorf("invalid function")
}

func (stmt *tokenBlock) parseNotFactStmt() (FactStmt, error) {
	stmt.header.skip()
	ret, err := stmt.parsePtyStmt()
	if err != nil {
		return nil, err
	}
	ret.setT(false)
	return ret, nil
}

func (stmt *tokenBlock) parseFuncPtyStmt() (*FuncPtyStmt, error) {
	stmt.header.skip()
	fc, err := stmt.header.parseFc()
	if err != nil {
		return nil, err
	}
	return &FuncPtyStmt{true, fc}, nil
}

func (stmt *tokenBlock) parseForallStmt() (*ForallStmt, error) {
	stmt.header.skip()

	typeParams := &[]typeConceptPair{}
	var err error = nil
	if stmt.header.is(BuiltinSyms["["]) {
		typeParams, err = stmt.header.parseBracketedVarTypePair()
		if err != nil {
			return nil, err
		}
	}

	varParams, err := stmt.header.parseForallVarTypePairArrEndWithColon()
	if err != nil {
		return nil, err
	}

	ifFacts := &[]FactStmt{}
	thenFacts := &[]FactStmt{}

	if len(stmt.body) > 0 && (stmt.body)[0].header.is(Keywords["if"]) {
		ifFacts, err = stmt.body[0].parseFactsBlock()
		if err != nil {
			return nil, err
		}

		if len(stmt.body) == 2 && (stmt.body)[1].header.is(Keywords["then"]) {
			thenFacts, err = stmt.body[1].parseFactsBlock()
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

func (stmt *tokenBlock) parseBodyFacts() (*[]FactStmt, error) {
	if len(stmt.body) == 0 {
		return &[]FactStmt{}, nil
	}

	facts := &[]FactStmt{}
	for _, f := range stmt.body {
		fact, err := f.parseFactStmt()
		if err != nil {
			return nil, err
		}
		*facts = append(*facts, fact)
	}

	return facts, nil
}

func (stmt *tokenBlock) parseFactsBlock() (*[]FactStmt, error) {
	ifFacts := &[]FactStmt{}
	stmt.header.skip()
	if err := stmt.header.testAndSkip(BuiltinSyms[":"]); err != nil {
		return nil, err
	}

	for _, curStmt := range stmt.body {
		fact, err := curStmt.parseFactStmt()
		if err != nil {
			return nil, err
		}
		*ifFacts = append(*ifFacts, fact)
	}

	return ifFacts, nil
}

func (stmt *tokenBlock) parseDefPropertyStmt() (*DefPropertyStmt, error) {
	decl, err := stmt.header.parsePropertyDecl()
	if err != nil {
		return nil, err
	}

	ifFacts := &[]FactStmt{}
	thenFacts := &[]FactStmt{}
	if stmt.header.is(BuiltinSyms[":"]) {
		stmt.header.skip()

		if len(stmt.body) == 2 && stmt.body[0].header.is(Keywords["if"]) && stmt.body[1].header.is(Keywords["then"]) {
			stmt.body[0].header.skip()
			if err := stmt.body[0].header.testAndSkip(BuiltinSyms[":"]); err != nil {
				return nil, err
			}

			ifFacts, err = stmt.body[0].parseBodyFacts()
			if err != nil {
				return nil, err
			}

			stmt.body[1].header.skip()
			if err := stmt.body[1].header.testAndSkip(BuiltinSyms[":"]); err != nil {
				return nil, err
			}

			thenFacts, err = stmt.body[1].parseBodyFacts()
			if err != nil {
				return nil, err
			}
		} else {
			thenFacts, err = stmt.parseBodyFacts()
			if err != nil {
				return nil, err
			}
		}
	}

	return &DefPropertyStmt{*decl, *ifFacts, *thenFacts}, nil
}

func (stmt *tokenBlock) parseInherit() (*[]typeConcept, error) {
	stmt.header.skip(Keywords["inherit"])

	if err := stmt.header.testAndSkip(BuiltinSyms[":"]); err != nil {
		return nil, err
	}

	types := []typeConcept{}
	for _, curStmt := range stmt.body {
		cur, err := curStmt.header.next()
		if err != nil {
			return nil, err
		}
		types = append(types, typeConcept(cur))
		if !curStmt.header.isEnd() {
			return nil, fmt.Errorf("expect one string in inherit")
		}
	}
	return &types, nil
}

func (stmt *tokenBlock) parseLocalStmt() (*localStmt, error) {
	stmt.header.skip(Keywords["local"])

	if err := stmt.header.testAndSkip(BuiltinSyms[":"]); err != nil {
		return nil, err
	}

	localStatements := []Stmt{}
	for _, curStmt := range stmt.body {
		localStmt, err := curStmt.ParseStmt()
		if err != nil {
			return nil, err
		}
		localStatements = append(localStatements, localStmt)
	}

	return &localStmt{localStatements}, nil
}
