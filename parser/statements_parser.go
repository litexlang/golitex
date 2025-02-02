package parser

import (
	"fmt"
	"strings"
)

func parseSourceCode(code string) (*[]topStmt, error) {
	code = strings.ReplaceAll(code, "\t", "    ")

	slice, err := getTopLevelStmtSlice(code)
	if err != nil {
		return nil, err
	}

	blocks := []tokenBlock{}
	for _, strBlock := range slice.body {
		block, err := TokenizeStmtBlock(&strBlock)
		if err != nil {
			return nil, err
		}
		blocks = append(blocks, *block)
	}

	ret := []topStmt{}
	for _, block := range blocks {
		cur, err := block.ParseTopLevelStmt()
		if err != nil {
			return nil, err
		}
		ret = append(ret, *cur)
		fmt.Printf("%v\n", cur)
	}

	return &ret, nil
}

func (stmt *tokenBlock) ParseTopLevelStmt() (*topStmt, error) {
	pub := false
	if stmt.header.is(BuiltinSyms["pub"]) {
		stmt.header.skip()
		pub = true
	}

	ret, err := stmt.ParseStmt()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	return &topStmt{ret, pub}, nil
}

func (stmt *tokenBlock) ParseStmt() (Stmt, error) {
	cur, err := stmt.header.currentToken()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
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
	case Keywords["use"]:
		return stmt.parseDefUseStmt()
	case Keywords["know"]:
		return stmt.parseKnowStmt()
	case Keywords["exist"]:
		return stmt.parseExistStmt()
	case Keywords["have"]:
		return stmt.parseHaveStmt()
	case Keywords["member"]:
		return stmt.parseMemberStmt()
	case Keywords["type_member"]:
		return stmt.parseTypeMemberStmt()
	default:
		return stmt.parseFactStmt()
	}
}

func (p *tokenBlock) parseFcMember() (*[]fcVarDecl, *[]fcFnDecl, *[]propertyDecl, error) {
	p.header.next()
	if err := p.header.testAndSkip(BuiltinSyms[":"]); err != nil {
		return nil, nil, nil, err
	}

	varMember := &[]fcVarDecl{}
	fnMember := &[]fcFnDecl{}
	propertyMember := &[]propertyDecl{}

	for _, curStmt := range p.body {
		if curStmt.header.is(Keywords["var"]) {
			member, err := curStmt.header.parseVarDecl()
			if err != nil {
				return nil, nil, nil, err
			}
			*varMember = append(*varMember, *member)
		} else if curStmt.header.is(Keywords["fn"]) {
			member, err := curStmt.header.parseFcFnDecl()
			if err != nil {
				return nil, nil, nil, err
			}
			*fnMember = append(*fnMember, *member)
		} else if curStmt.header.is(Keywords["property"]) {
			member, err := curStmt.header.parsePropertyDecl()
			if err != nil {
				return nil, nil, nil, err
			}
			*propertyMember = append(*propertyMember, *member)
		}
	}

	return varMember, fnMember, propertyMember, nil
}

func (stmt *tokenBlock) parseThenFacts() (*[]factStmt, error) {
	stmt.header.next()
	if err := stmt.header.testAndSkip(BuiltinSyms[":"]); err != nil {
		return nil, err
	}

	facts := &[]factStmt{}

	for _, curStmt := range stmt.body {
		if curStmt.header.is(Keywords["fact"]) {
			fact, err := curStmt.parseFactStmt()
			if err != nil {
				return nil, err
			}
			*facts = append(*facts, fact)
		}
	}

	return facts, nil
}

func (p *tokenBlock) parseFnRetTypeMember() (*[]fnRetTypeMemberDecl, error) {
	p.header.next()
	if err := p.header.testAndSkip(BuiltinSyms[":"]); err != nil {
		return nil, err
	}

	member := &[]fnRetTypeMemberDecl{}

	for _, curStmt := range p.body {
		if curStmt.header.is(Keywords["var"]) {
			v, err := curStmt.header.parseVarDecl()
			if err != nil {
				return nil, err
			}
			*member = append(*member, v)
		} else if curStmt.header.is(Keywords["fn"]) {
			v, err := curStmt.header.parseFcFnDecl()
			if err != nil {
				return nil, err
			}
			*member = append(*member, v)

		} else {
			return nil, fmt.Errorf("unexpected declaration %v", curStmt.header)
		}
	}

	return member, nil
}

func (stmt *tokenBlock) parseDefConceptStmt() (*defConceptStmt, error) {
	stmt.header.skip()

	typeVariable, err := stmt.header.next()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	conceptName, err := stmt.header.next()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	if !stmt.header.is(BuiltinSyms[":"]) {
		return &defConceptStmt{typeVarStr(typeVariable), typeConceptStr(conceptName), []typeConceptStr{}, []fcVarDecl{}, []fcFnDecl{}, []propertyDecl{}, []fcVarDecl{}, []fcFnDecl{}, []propertyDecl{}, []factStmt{}}, nil
	} else {
		stmt.header.next()
	}

	inherit := &[]typeConceptStr{}
	typeVarMember := &[]fcVarDecl{}
	typeFnMember := &[]fcFnDecl{}
	typePropertyMember := &[]propertyDecl{}
	varMember := &[]fcVarDecl{}
	fnMember := &[]fcFnDecl{}
	propertyMember := &[]propertyDecl{}
	thenFacts := &[]factStmt{}

	for _, curStmt := range stmt.body {
		if curStmt.header.is(Keywords["inherit"]) {
			inherit, err = curStmt.parseInherit()
			if err != nil {
				return nil, &parseStmtErr{err, *stmt}
			}
		} else if curStmt.header.is(Keywords["type_member"]) {
			typeVarMember, typeFnMember, typePropertyMember, err = curStmt.parseFcMember()
			if err != nil {
				return nil, &parseStmtErr{err, *stmt}
			}
		} else if curStmt.header.is(Keywords["member"]) {
			varMember, fnMember, propertyMember, err = curStmt.parseFcMember()
			if err != nil {
				return nil, &parseStmtErr{err, *stmt}
			}
		} else if curStmt.header.is(Keywords["then"]) {
			thenFacts, err = curStmt.parseThenFacts()
			if err != nil {
				return nil, &parseStmtErr{err, *stmt}
			}
		}
	}

	return &defConceptStmt{typeVarStr(typeVariable), typeConceptStr(conceptName), *inherit, *typeVarMember, *typeFnMember, *typePropertyMember, *varMember, *fnMember, *propertyMember, *thenFacts}, nil

}

func (stmt *tokenBlock) parseDefTypeStmt() (*defTypeStmt, error) {
	stmt.header.skip()

	typeVariable, err := stmt.header.next()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	conceptName, err := stmt.header.next()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	if !stmt.header.is(BuiltinSyms[":"]) {
		return &defTypeStmt{typeVarStr(typeVariable), typeConceptStr(conceptName), []fcVarDecl{}, []fcFnDecl{}, []propertyDecl{}, []factStmt{}}, nil
	} else {
		stmt.header.next()
	}

	varMember := &[]fcVarDecl{}
	fnMember := &[]fcFnDecl{}
	propertyMember := &[]propertyDecl{}
	thenFacts := &[]factStmt{}

	if len(stmt.body) == 2 && stmt.body[0].header.is(Keywords["member"]) && stmt.body[1].header.is(Keywords["then"]) {
		varMember, fnMember, propertyMember, err = stmt.body[0].parseFcMember()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}

		thenFacts, err = stmt.body[1].parseThenFacts()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
	} else {
		thenFacts, err = stmt.parseBodyFacts()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
	}

	return &defTypeStmt{typeVarStr(typeVariable), typeConceptStr(conceptName), *varMember, *fnMember, *propertyMember, *thenFacts}, nil

}

func (stmt *tokenBlock) parseFactStmt() (factStmt, error) {
	if stmt.header.is(Keywords["forall"]) {
		return stmt.parseForallStmt()
	}

	return stmt.parseNotFactStmt()
}

func (stmt *tokenBlock) parseNotFactStmt() (notFactStmt, error) {
	isTrue := true
	if stmt.header.is(BuiltinSyms["not"]) {
		err := stmt.header.skip(BuiltinSyms["not"])
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		isTrue = false
	}

	var ret notFactStmt
	var err error = nil
	if stmt.header.is(BuiltinSyms["$"]) {
		ret, err = stmt.parseFuncPropertyFactStmt()
	} else {
		ret, err = stmt.parseRelationalFactStmt()
	}

	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	ret.setT(isTrue)
	return ret, nil
}

func (stmt *tokenBlock) parseFuncPropertyFactStmt() (*funcPtyStmt, error) {
	err := stmt.header.skip(BuiltinSyms["$"])
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	fc, err := stmt.header.parseFcFnRetVal()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}
	return &funcPtyStmt{true, fc}, nil
}

func (stmt *tokenBlock) parseForallStmt() (*forallStmt, error) {
	stmt.header.skip()

	typeParams := &[]typeConceptPair{}
	var err error = nil
	if stmt.header.is(BuiltinSyms["["]) {
		typeParams, err = stmt.header.parseBracketedTypeConceptPairArray()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
	}

	varParams, err := stmt.header.parseFcVarTypePairArrEndWithColon()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	ifFacts := &[]factStmt{}
	thenFacts := &[]factStmt{}

	if len(stmt.body) > 0 && (stmt.body)[0].header.is(Keywords["if"]) {
		ifFacts, err = stmt.body[0].parseFactsBlock()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}

		if len(stmt.body) == 2 && (stmt.body)[1].header.is(Keywords["then"]) {
			thenFacts, err = stmt.body[1].parseFactsBlock()
			if err != nil {
				return nil, &parseStmtErr{err, *stmt}
			}
		} else {
			return nil, fmt.Errorf("expected 'then'")
		}
	} else {
		thenFacts, err = stmt.parseBodyFacts()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
	}

	return &forallStmt{*typeParams, *varParams, *ifFacts, *thenFacts}, nil
}

func (stmt *tokenBlock) parseBodyFacts() (*[]factStmt, error) {
	if len(stmt.body) == 0 {
		return &[]factStmt{}, nil
	}

	facts := &[]factStmt{}
	for _, f := range stmt.body {
		fact, err := f.parseFactStmt()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		*facts = append(*facts, fact)
	}

	return facts, nil
}

func (stmt *tokenBlock) parseFactsBlock() (*[]factStmt, error) {
	ifFacts := &[]factStmt{}
	stmt.header.skip()
	if err := stmt.header.testAndSkip(BuiltinSyms[":"]); err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	for _, curStmt := range stmt.body {
		fact, err := curStmt.parseFactStmt()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		*ifFacts = append(*ifFacts, fact)
	}

	return ifFacts, nil
}

func (stmt *tokenBlock) parseDefPropertyStmt() (*defPropertyStmt, error) {
	decl, err := stmt.header.parsePropertyDecl()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	ifFacts := &[]factStmt{}
	thenFacts := &[]factStmt{}
	if stmt.header.is(BuiltinSyms[":"]) {
		stmt.header.skip()
		ifFacts, thenFacts, err = stmt.parseBodyIfFactsThenFacts()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
	}

	return &defPropertyStmt{*decl, *ifFacts, *thenFacts}, nil
}

func (stmt *tokenBlock) parseInherit() (*[]typeConceptStr, error) {
	stmt.header.skip(Keywords["inherit"])

	if err := stmt.header.testAndSkip(BuiltinSyms[":"]); err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	types := []typeConceptStr{}
	for _, curStmt := range stmt.body {
		cur, err := curStmt.header.next()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		types = append(types, typeConceptStr(cur))
		if !curStmt.header.isEnd() {
			return nil, fmt.Errorf("expect one string in inherit")
		}
	}
	return &types, nil
}

func (stmt *tokenBlock) parseLocalStmt() (*localStmt, error) {
	stmt.header.skip(Keywords["local"])

	if err := stmt.header.testAndSkip(BuiltinSyms[":"]); err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	localStatements := []Stmt{}
	for _, curStmt := range stmt.body {
		localStmt, err := curStmt.ParseStmt()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		localStatements = append(localStatements, localStmt)
	}

	return &localStmt{localStatements}, nil
}

func (stmt *tokenBlock) parseBodyIfFactsThenFacts() (*[]factStmt, *[]factStmt, error) {
	ifFacts := &[]factStmt{}
	thenFacts := &[]factStmt{}
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

func (stmt *tokenBlock) parseDefFnStmt() (*defFnStmt, error) {
	stmt.header.skip(Keywords["fn"])

	decl, err := stmt.header.parseFcFnDecl()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	ifFacts := &[]factStmt{}
	thenFacts := &[]factStmt{}

	if stmt.header.is(BuiltinSyms[":"]) {
		stmt.header.skip()
		ifFacts, thenFacts, err = stmt.parseBodyIfFactsThenFacts()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
	}

	return &defFnStmt{*decl, *ifFacts, *thenFacts}, nil
}

func (stmt *tokenBlock) parseDefVarStmt() (*defVarStmt, error) {
	decl, err := stmt.header.parseVarDecl()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	ifFacts := &[]factStmt{}

	if stmt.header.is(BuiltinSyms[":"]) {
		stmt.header.skip()
		ifFacts, err = stmt.parseBodyFacts()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
	} else if !stmt.header.isEnd() {
		return nil, fmt.Errorf("expect ':' or end of block")
	}

	return &defVarStmt{*decl, *ifFacts}, nil
}

func (stmt *tokenBlock) parseClaimStmt() (*claimStmt, error) {
	stmt.header.skip()
	var err error = nil

	if err := stmt.header.testAndSkip(BuiltinSyms[":"]); err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	toCheck := &[]factStmt{}
	proof := &[]Stmt{}

	for i := 0; i < len(stmt.body)-1; i++ {
		if !stmt.header.is(Keywords["proof"]) {
			fact, err := stmt.body[i].parseFactStmt()
			if err != nil {
				return nil, &parseStmtErr{err, *stmt}
			}
			*toCheck = append(*toCheck, fact)
		}
	}

	err = stmt.body[len(stmt.body)-1].header.testAndSkip(Keywords["proof"])
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	err = stmt.body[len(stmt.body)-1].header.testAndSkip(Keywords[":"])
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	for _, block := range stmt.body[len(stmt.body)-1].body {
		curStmt, err := block.ParseStmt()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		*proof = append(*proof, curStmt)
	}

	return &claimStmt{*toCheck, *proof}, nil
}

func (stmt *tokenBlock) parseDefUseStmt() (*defuseStmt, error) {
	stmt.header.skip(Keywords["use"])

	name, err := stmt.header.next()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	variable, err := stmt.header.parseFcAtom()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	return &defuseStmt{name, variable}, nil
}

func (stmt *tokenBlock) parseKnowStmt() (*knowStmt, error) {
	stmt.header.skip(Keywords["know"])

	if err := stmt.header.testAndSkip(BuiltinSyms[":"]); err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	facts, err := stmt.parseBodyFacts()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	return &knowStmt{*facts}, nil
}

func (stmt *tokenBlock) parseExistStmt() (*defExistStmt, error) {
	decl, err := stmt.header.parseExistDecl()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	ifFacts := &[]factStmt{}
	member := &[]fnRetTypeMemberDecl{}
	thenFacts := &[]factStmt{}
	if !stmt.header.is(BuiltinSyms[":"]) {
		return nil, fmt.Errorf("expected ':‘")
	}

	stmt.header.skip(BuiltinSyms[":"])

	for _, curStmt := range stmt.body {
		if curStmt.header.is(Keywords["if"]) {
			ifFacts, err = curStmt.parseBodyFacts()
			if err != nil {
				return nil, &parseStmtErr{err, *stmt}
			}
			continue
		}
		if curStmt.header.is(Keywords["then"]) {
			thenFacts, err = curStmt.parseBodyFacts()
			if err != nil {
				return nil, &parseStmtErr{err, *stmt}
			}
			continue
		}
		if curStmt.header.is(Keywords["members"]) {
			member, err = curStmt.parseFnRetTypeMember()
			if err != nil {
				return nil, &parseStmtErr{err, *stmt}
			}
			continue
		}
	}

	return &defExistStmt{*decl, *ifFacts, *member, *thenFacts}, nil
}

func (stmt *tokenBlock) parseHaveStmt() (*haveStmt, error) {
	stmt.header.skip(Keywords["have"])
	propertyStmt, err := stmt.parseFuncPropertyFactStmt()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	if !stmt.header.is(BuiltinSyms[":"]) {
		return nil, fmt.Errorf("expected ':'")
	}

	if len(stmt.body) != 1 {
		return nil, fmt.Errorf("expect one string in members")
	}

	members, err := stmt.body[0].header.parseStringArr()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	if !stmt.body[0].header.isEnd() {
		return nil, fmt.Errorf("expected end of block")
	}

	return &haveStmt{propertyStmt, *members}, nil
}

func (stmt *tokenBlock) parseMemberStmt() (*defMemberStmt, error) {
	stmt.header.skip(Keywords["member"])

	typeConcepts, err := stmt.header.parseBracketedTypeConceptPairArray()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	if len(*typeConcepts) != 1 {
		return nil, fmt.Errorf("expect one type concept in members")
	}

	typeConcept := (*typeConcepts)[0]

	varTypes, err := stmt.header.parseBracedFcStrTypePairArray()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	if len(*varTypes) != 1 {
		return nil, fmt.Errorf("expect one type in members")
	}

	varType := (*varTypes)[0]

	var decl fcDecl

	if stmt.header.is(Keywords["var"]) {
		decl, err = stmt.header.parseVarDecl()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
	} else if stmt.header.is(Keywords["fn"]) {
		decl, err = stmt.header.parseFcFnDecl()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
	} else if stmt.header.is(Keywords["property"]) {
		decl, err = stmt.header.parsePropertyDecl()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
	} else {
		return nil, fmt.Errorf("expect 'var', 'fn', or 'property'")
	}

	if stmt.header.isEnd() {
		return &defMemberStmt{typeConcept, varType, decl, []factStmt{}}, nil
	}

	if err := stmt.header.testAndSkip(BuiltinSyms[":"]); err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	facts, err := stmt.parseBodyFacts()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	return &defMemberStmt{typeConcept, varType, decl, *facts}, nil
}

func (stmt *tokenBlock) parseTypeMemberStmt() (*defTypeMemberStmt, error) {
	stmt.header.skip(Keywords["type_member"])

	typeConcepts, err := stmt.header.parseBracketedTypeConceptPairArray()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	if len(*typeConcepts) != 1 {
		return nil, fmt.Errorf("expect one type concept in members")
	}

	typeConcept := (*typeConcepts)[0]

	var decl fcDecl

	if stmt.header.is(Keywords["var"]) {
		decl, err = stmt.header.parseVarDecl()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
	} else if stmt.header.is(Keywords["fn"]) {
		decl, err = stmt.header.parseFcFnDecl()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
	} else if stmt.header.is(Keywords["property"]) {
		decl, err = stmt.header.parsePropertyDecl()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
	} else {
		return nil, fmt.Errorf("expect 'var', 'fn', or 'property'")
	}

	if stmt.header.isEnd() {
		return &defTypeMemberStmt{typeConcept, decl, []factStmt{}}, nil
	}

	if err := stmt.header.testAndSkip(BuiltinSyms[":"]); err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	facts, err := stmt.parseBodyFacts()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	return &defTypeMemberStmt{typeConcept, decl, *facts}, nil
}

func (stmt *tokenBlock) parseRelationalFactStmt() (notFactStmt, error) {
	fc, err := stmt.header.parseFcExpr()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	opt, err := stmt.header.next()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	if opt == Keywords["is"] {
		return stmt.header.parseIsExpr(fc)
	}

	if !isBuiltinRelationalOperator(opt) {
		return nil, &parseStmtErr{err, *stmt}
	}

	fc2, err := stmt.header.parseFcExpr()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	vars := []Fc{fc, fc2}
	for stmt.header.is(opt) {
		stmt.header.skip()
		fc, err := stmt.header.parseFcExpr()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		vars = append(vars, fc)
	}

	return &relationFactStmt{true, vars, FcStr(opt)}, nil
}
