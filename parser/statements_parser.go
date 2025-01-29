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
	case Keywords["type"]:
		return stmt.parseDefTypeStmt()
	case Keywords["property"]:
		return stmt.parseDefPropertyStmt()
	case Keywords["fn"]:
		return stmt.parseDefFnStmt()
	case Keywords["local"]:
		return stmt.parseLocalStmt()
	case Keywords["var"]:
		return stmt.parseDefVarStmt()
	case Keywords["claim"]:
		return stmt.parseClaimStmt()
	case Keywords["alias"]:
		return stmt.parseDefAliasStmt()
	case Keywords["know"]:
		return stmt.parseKnowStmt()
	case Keywords["exist"]:
		return stmt.parseExistStmt()
	default:
		return stmt.parseFactStmt()
	}
}

func (stmt *tokenBlock) parseDefConceptStmt() (*DefConceptStmt, error) {
	stmt.header.skip()

	typeVariable, err := stmt.header.next()
	if err != nil {
		return nil, err
	}

	conceptName, err := stmt.header.next()
	if err != nil {
		return nil, err
	}

	if !stmt.header.is(BuiltinSyms[":"]) {
		return &DefConceptStmt{typeVar(typeVariable), typeConcept(conceptName), []typeConcept{}, []fcVarDecl{}, []fcFnDecl{}, []propertyDecl{}, []fcVarDecl{}, []fcFnDecl{}, []propertyDecl{}, []FactStmt{}}, nil
	} else {
		stmt.header.next()
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
			typeVarMember, typeFnMember, typePropertyMember, err = curStmt.parseFcMember()
			if err != nil {
				return nil, err
			}
		} else if curStmt.header.is(Keywords["member"]) {
			varMember, fnMember, propertyMember, err = curStmt.parseFcMember()
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

	return &DefConceptStmt{typeVar(typeVariable), typeConcept(conceptName), *inherit, *typeVarMember, *typeFnMember, *typePropertyMember, *varMember, *fnMember, *propertyMember, *thenFacts}, nil

}

func (stmt *tokenBlock) parseDefTypeStmt() (*DefTypeStmt, error) {
	stmt.header.skip()

	typeVariable, err := stmt.header.next()
	if err != nil {
		return nil, err
	}

	conceptName, err := stmt.header.next()
	if err != nil {
		return nil, err
	}

	if !stmt.header.is(BuiltinSyms[":"]) {
		return &DefTypeStmt{typeVar(typeVariable), typeConcept(conceptName), []fcVarDecl{}, []fcFnDecl{}, []propertyDecl{}, []FactStmt{}}, nil
	} else {
		stmt.header.next()
	}

	varMember := &[]fcVarDecl{}
	fnMember := &[]fcFnDecl{}
	propertyMember := &[]propertyDecl{}
	thenFacts := &[]FactStmt{}

	if len(stmt.body) == 2 && stmt.body[0].header.is(Keywords["member"]) && stmt.body[1].header.is(Keywords["then"]) {
		varMember, fnMember, propertyMember, err = stmt.body[0].parseFcMember()
		if err != nil {
			return nil, err
		}

		thenFacts, err = stmt.body[1].parseThenFacts()
		if err != nil {
			return nil, err
		}
	} else {
		thenFacts, err = stmt.parseBodyFacts()
		if err != nil {
			return nil, err
		}
	}

	return &DefTypeStmt{typeVar(typeVariable), typeConcept(conceptName), *varMember, *fnMember, *propertyMember, *thenFacts}, nil

}

func (stmt *tokenBlock) parseFactStmt() (FactStmt, error) {
	if stmt.header.is(Keywords["forall"]) {
		return stmt.parseForallStmt()
	}

	if stmt.header.is(Keywords["not"]) {
		return stmt.parseNotFactStmt()
	}

	return stmt.parsePropertyFactStmt()
}

func (stmt *tokenBlock) parsePropertyFactStmt() (propertyFactStmt, error) {
	if stmt.header.is(BuiltinSyms["$"]) {
		return stmt.parseFuncPtyStmt()
	}

	return nil, fmt.Errorf("invalid function")
}

func (stmt *tokenBlock) parseNotFactStmt() (FactStmt, error) {
	stmt.header.skip()
	ret, err := stmt.parsePropertyFactStmt()
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

	varParams, err := stmt.header.parseFcVarTypePairArrEndWithColon()
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
		ifFacts, thenFacts, err = stmt.parseBodyIfFactsThenFacts()
		if err != nil {
			return nil, err
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

func (stmt *tokenBlock) parseBodyIfFactsThenFacts() (*[]FactStmt, *[]FactStmt, error) {
	ifFacts := &[]FactStmt{}
	thenFacts := &[]FactStmt{}
	var err error = nil

	if len(stmt.body) == 2 && stmt.body[0].header.is(Keywords["if"]) && stmt.body[1].header.is(Keywords["then"]) {
		stmt.body[0].header.skip()
		if err := stmt.body[0].header.testAndSkip(BuiltinSyms[":"]); err != nil {
			return nil, nil, err
		}

		ifFacts, err = stmt.body[0].parseBodyFacts()
		if err != nil {
			return nil, nil, err
		}

		stmt.body[1].header.skip()
		if err := stmt.body[1].header.testAndSkip(BuiltinSyms[":"]); err != nil {
			return nil, nil, err
		}

		thenFacts, err = stmt.body[1].parseBodyFacts()
		if err != nil {
			return nil, nil, err
		}
	} else {
		thenFacts, err = stmt.parseBodyFacts()
		if err != nil {
			return nil, nil, err
		}
	}

	return ifFacts, thenFacts, nil
}

func (stmt *tokenBlock) parseDefFnStmt() (*DefFnStmt, error) {
	stmt.header.skip(Keywords["fn"])

	decl, err := stmt.header.parseFcFnDecl()
	if err != nil {
		return nil, err
	}

	ifFacts := &[]FactStmt{}
	thenFacts := &[]FactStmt{}

	if stmt.header.is(BuiltinSyms[":"]) {
		stmt.header.skip()
		ifFacts, thenFacts, err = stmt.parseBodyIfFactsThenFacts()
		if err != nil {
			return nil, err
		}
	}

	return &DefFnStmt{*decl, *ifFacts, *thenFacts}, nil
}

func (stmt *tokenBlock) parseDefVarStmt() (*DefVarStmt, error) {
	decl, err := stmt.header.parseVarDecl()
	if err != nil {
		return nil, err
	}

	ifFacts := &[]FactStmt{}

	if stmt.header.is(BuiltinSyms[":"]) {
		stmt.header.skip()
		ifFacts, err = stmt.parseBodyFacts()
		if err != nil {
			return nil, err
		}
	}

	return &DefVarStmt{*decl, *ifFacts}, nil
}

func (stmt *tokenBlock) parseClaimStmt() (*claimStmt, error) {
	stmt.header.skip()
	var err error = nil

	if err := stmt.header.testAndSkip(BuiltinSyms[":"]); err != nil {
		return nil, err
	}

	toCheck := &[]FactStmt{}
	proof := &[]Stmt{}

	for i := 0; i < len(stmt.body)-1; i++ {
		if !stmt.header.is(Keywords["proof"]) {
			fact, err := stmt.body[i].parseFactStmt()
			if err != nil {
				return nil, err
			}
			*toCheck = append(*toCheck, fact)
		}
	}

	err = stmt.body[len(stmt.body)-1].header.testAndSkip(Keywords["proof"])
	if err != nil {
		return nil, err
	}

	err = stmt.body[len(stmt.body)-1].header.testAndSkip(Keywords[":"])
	if err != nil {
		return nil, err
	}

	for _, block := range stmt.body[len(stmt.body)-1].body {
		curStmt, err := block.ParseStmt()
		if err != nil {
			return nil, err
		}
		*proof = append(*proof, curStmt)
	}

	return &claimStmt{*toCheck, *proof}, nil
}

func (stmt *tokenBlock) parseDefAliasStmt() (*defAliasStmt, error) {
	stmt.header.skip(Keywords["alias"])

	name, err := stmt.header.next()
	if err != nil {
		return nil, err
	}

	variable, err := stmt.header.parseFc()
	if err != nil {
		return nil, err
	}

	return &defAliasStmt{name, variable}, nil
}

func (stmt *tokenBlock) parseKnowStmt() (*knowStmt, error) {
	stmt.header.skip(Keywords["know"])

	if err := stmt.header.testAndSkip(BuiltinSyms[":"]); err != nil {
		return nil, err
	}

	facts, err := stmt.parseBodyFacts()
	if err != nil {
		return nil, err
	}

	return &knowStmt{*facts}, nil
}

func (stmt *tokenBlock) parseExistStmt() (*defExistStmt, error) {
	decl, err := stmt.header.parseExistDecl()
	if err != nil {
		return nil, err
	}

	ifFacts := &[]FactStmt{}
	member := &[]fnRetTypeMemberDecl{}
	thenFacts := &[]FactStmt{}
	if !stmt.header.is(BuiltinSyms[":"]) {
		return nil, fmt.Errorf("expected ':‘")
	}

	stmt.header.skip(BuiltinSyms[":"])

	for _, curStmt := range stmt.body {
		if curStmt.header.is(Keywords["if"]) {
			ifFacts, err = curStmt.parseBodyFacts()
			if err != nil {
				return nil, err
			}
			continue
		}
		if curStmt.header.is(Keywords["then"]) {
			thenFacts, err = curStmt.parseBodyFacts()
			if err != nil {
				return nil, err
			}
			continue
		}
		if curStmt.header.is(Keywords["members"]) {
			member, err = curStmt.parseFnRetTypeMember()
			if err != nil {
				return nil, err
			}
			continue
		}
	}

	return &defExistStmt{*decl, *ifFacts, *member, *thenFacts}, nil
}
