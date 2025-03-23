package litexparser

import (
	"fmt"
)

func (stmt *TokenBlock) ParseTopLevelStmt() (*TopStmt, error) {
	pub := false
	if stmt.Header.is(KeywordPub) {
		stmt.Header.skip()
		pub = true
	}

	ret, err := stmt.ParseStmt()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	return &TopStmt{ret, pub}, nil
}

func (stmt *TokenBlock) ParseStmt() (Stmt, error) {
	cur, err := stmt.Header.currentToken()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	var ret Stmt
	switch cur {
	case KeywordInterface:
		ret, err = stmt.parseDefSetStructStmt()
	case KeywordType:
		ret, err = stmt.parseDefTypeStmt()
	case KeywordProp:
		ret, err = stmt.parseDefPropStmt()
	case KeywordFn:
		ret, err = stmt.parseDefFnStmt()
	case KeywordObj:
		ret, err = stmt.parseDefObjStmt()
	case KeywordClaim:
		ret, err = stmt.parseClaimStmt()
	case KeywordProve:
		ret, err = stmt.parseProveClaimStmt()
	case KeywordKnow:
		ret, err = stmt.parseKnowStmt()
	case KeywordExistProp:
		ret, err = stmt.parseDefExistStmt()
	case KeywordHave:
		ret, err = stmt.parseHaveStmt()
	case KeywordAxiom:
		ret, err = stmt.parseAxiomStmt()
	case KeywordThm:
		ret, err = stmt.parseThmStmt()
	default:
		ret, err = stmt.parseFactStmt()
	}

	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	if !stmt.Header.ExceedEnd() {
		return nil, &parseStmtErr{err, *stmt}
	}

	return ret, nil
}

func (stmt *TokenBlock) parseTypeConceptDeclStmtKnows() (*[]FactStmt, error) {
	stmt.Header.next()
	if err := stmt.Header.testAndSkip(KeywordColon); err != nil {
		return nil, err
	}

	facts := &[]FactStmt{}

	for _, curStmt := range stmt.Body {
		fact, err := curStmt.parseFactStmt()
		if err != nil {
			return nil, err
		}
		*facts = append(*facts, fact)
	}

	return facts, nil
}

func (block *TokenBlock) parseDefSetStructStmt() (*DefInterfaceStmt, error) {
	block.Header.skip(KeywordInterface)

	decl, err := block.Header.next()
	if err != nil {
		return nil, &parseStmtErr{err, *block}
	}

	structNameStr := ""
	if block.Header.is(KeywordImpl) {
		block.Header.next()
		structNameStr, err = block.Header.next()
		if err != nil {
			return nil, &parseStmtErr{err, *block}
		}
	}
	structName := TypeConceptStr(structNameStr)

	if !block.Header.is(KeywordColon) {
		return &DefInterfaceStmt{decl, structName, []TypeMember{}, []InstanceMember{}, []FactStmt{}}, nil
	} else {
		block.Header.next()
	}

	typeMembers := []TypeMember{}
	instanceMembers := []InstanceMember{}
	knowFacts := &[]FactStmt{}

	for _, curStmt := range block.Body {
		if curStmt.Header.is(KeywordTypeMember) {
			for _, member := range curStmt.Body {
				typeMember, err := member.parseTypeMember()
				if err != nil {
					return nil, &parseStmtErr{err, *block}
				}
				typeMembers = append(typeMembers, typeMember)
			}
		} else if curStmt.Header.is(KeywordInstanceMember) {
			for _, member := range curStmt.Body {
				instanceMember, err := member.parseInstanceMember()
				if err != nil {
					return nil, &parseStmtErr{err, *block}
				}
				instanceMembers = append(instanceMembers, instanceMember)
			}
		} else if curStmt.Header.is(KeywordKnow) {
			knowFacts, err = curStmt.parseTypeConceptDeclStmtKnows()
			if err != nil {
				return nil, &parseStmtErr{err, *block}
			}
		}
	}

	return &DefInterfaceStmt{decl, structName, typeMembers, instanceMembers, *knowFacts}, nil

}

func (block *TokenBlock) parseDefTypeStmt() (*DefTypeStmt, error) {
	err := block.Header.skip(KeywordType)
	if err != nil {
		return nil, &parseStmtErr{err, *block}
	}

	// implName := &NamedFcType{}

	// if block.Header.is(Keywords["impl"]) {
	// 	block.Header.next()
	// 	implName, err = block.Header.parseNamedFcType()
	// 	if err != nil {
	// 		return nil, &parseStmtErr{err, *block}
	// 	}
	// }

	decl, err := block.Header.next()
	if err != nil {
		return nil, &parseStmtErr{err, *block}
	}

	if !block.Header.is(KeywordColon) {
		return &DefTypeStmt{decl, []TypeMember{}, []InstanceMember{}, []FactStmt{}}, nil
	} else {
		block.Header.next()
	}

	typeMembers := []TypeMember{}
	instanceMembers := []InstanceMember{}
	knowFacts := &[]FactStmt{}

	for _, curStmt := range block.Body {
		if curStmt.Header.is(KeywordTypeMember) {
			for _, member := range curStmt.Body {
				typeMember, err := member.parseTypeMember()
				if err != nil {
					return nil, &parseStmtErr{err, *block}
				}
				typeMembers = append(typeMembers, typeMember)
			}

		} else if curStmt.Header.is(KeywordInstanceMember) {
			for _, member := range curStmt.Body {
				instanceMember, err := member.parseInstanceMember()
				if err != nil {
					return nil, &parseStmtErr{err, *block}
				}
				instanceMembers = append(instanceMembers, instanceMember)
			}

		} else if curStmt.Header.is(KeywordKnow) {
			knowFacts, err = curStmt.parseTypeConceptDeclStmtKnows()
			if err != nil {
				return nil, &parseStmtErr{err, *block}
			}
		} else {
			return nil, &parseStmtErr{fmt.Errorf("expected type_member or instance_member, got %s", curStmt.Header.strAtCurIndexPlus(0)), *block}
		}
	}
	return &DefTypeStmt{decl, typeMembers, instanceMembers, *knowFacts}, nil
}

func (stmt *TokenBlock) parseFactStmt() (FactStmt, error) {
	if stmt.Header.is(KeywordForall) {
		return stmt.parseForallStmt()
	} else if stmt.Header.is(KeywordWhen) {
		return stmt.parseIfStmt()
	}

	return stmt.parseInlineFactStmt()
}

func (stmt *TokenBlock) parseIfStmt() (FactStmt, error) {
	if stmt.Header.strAtIndex(-1) == KeywordColon {
		return stmt.parseBlockIfStmt()
	} else {
		return stmt.parseInlineIfFactStmt()
	}
}

func (stmt *TokenBlock) parseInlineFactStmt() (FactStmt, error) {
	if stmt.Header.is(KeywordWhen) {
		return stmt.parseInlineIfFactStmt()
	} else if stmt.Header.is(KeywordForall) {
		return stmt.parseInlineForallStmt()
	}

	return stmt.parseInstantiatedFactStmt()
}

func (stmt *TokenBlock) parseInlineForallStmt() (*BlockForallStmt, error) {
	err := stmt.Header.skip(KeywordForall)
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	varParams := &[]string{}
	condFacts := []FactStmt{}
	thenFacts := []SpecFactStmt{}

	for !stmt.Header.is(KeywordLeftCurly) {
		fact, err := stmt.parseInlineFactStmt()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		condFacts = append(condFacts, fact)

		if stmt.Header.is(KeywordComma) {
			stmt.Header.next()
		}
	}

	err = stmt.Header.skip(KeywordLeftCurly)
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	for !stmt.Header.is(KeywordRightCurly) {
		fact, err := stmt.parseInstantiatedFactStmt()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		thenFacts = append(thenFacts, fact)

		if stmt.Header.is(KeywordComma) {
			stmt.Header.next()
		}
	}
	err = stmt.Header.skip(KeywordRightCurly)
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	return &BlockForallStmt{*varParams, condFacts, thenFacts}, nil
}

func (stmt *TokenBlock) parseInstantiatedFactStmt() (SpecFactStmt, error) {
	isTrue := true
	if stmt.Header.is(KeywordNot) {
		err := stmt.Header.skip(KeywordNot)
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		isTrue = false
	}

	var ret SpecFactStmt
	var err error = nil
	if stmt.Header.is(KeywordDollar) {
		ret, err = stmt.parseFuncPropFactStmt()
	} else {
		ret, err = stmt.parseRelationalFactStmt()
	}

	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	ret.notFactStmtSetT(isTrue)
	return ret, nil
}

func (stmt *TokenBlock) parseFuncPropFactStmt() (*FuncFactStmt, error) {
	err := stmt.Header.skip(KeywordDollar)
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	opt, err := stmt.Header.parseFcAtom()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	params := []Fc{}
	err = stmt.Header.skip(KeywordLeftParen)
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	for !stmt.Header.is(KeywordRightParen) {
		param, err := stmt.Header.ParseFc()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		params = append(params, param)
		if stmt.Header.is(KeywordComma) {
			stmt.Header.next()
		}
	}

	err = stmt.Header.skip(KeywordRightParen)
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	return &FuncFactStmt{true, opt, params}, nil
}

func (stmt *TokenBlock) parseBlockedForall() (FactStmt, error) {
	err := stmt.Header.skip(KeywordForall)
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	varParams, err := stmt.Header.parseFcObjTypePairArrEndWithColon()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	ifFacts := &[]FactStmt{}
	thenFacts := &[]SpecFactStmt{}

	if len(stmt.Body) > 0 && (stmt.Body)[0].Header.is(KeywordCond) {
		ifFacts, err = stmt.Body[0].parseForallCondFactsBlock()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}

		if len(stmt.Body) == 2 && (stmt.Body)[1].Header.is(KeywordThen) {
			thenFacts, err = stmt.Body[1].parseInstantiatedFactsBlock()
			if err != nil {
				return nil, &parseStmtErr{err, *stmt}
			}
		} else {
			return nil, fmt.Errorf("expected 'then'")
		}
	} else {
		for _, curStmt := range stmt.Body {
			fact, err := curStmt.parseInstantiatedFactStmt()
			if err != nil {
				return nil, &parseStmtErr{err, *stmt}
			}
			*thenFacts = append(*thenFacts, fact)
		}
	}

	return &BlockForallStmt{*varParams, *ifFacts, *thenFacts}, nil
}

func (stmt *TokenBlock) parseForallStmt() (FactStmt, error) {
	if stmt.Header.strAtIndex(-1) != KeywordColon {
		return stmt.parseInlineForallStmt()
	} else {
		return stmt.parseBlockedForall()
	}
}

func (stmt *TokenBlock) parseBodyFacts() (*[]FactStmt, error) {
	facts := &[]FactStmt{}
	for _, f := range stmt.Body {
		fact, err := f.parseFactStmt()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		*facts = append(*facts, fact)
	}

	return facts, nil
}

func (stmt *TokenBlock) parseForallCondFactsBlock() (*[]FactStmt, error) {
	err := stmt.Header.parseGivenWordsThenExceedEnd(&[]string{KeywordCond, KeywordColon})
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	facts, err := stmt.parseBodyFacts()
	return facts, err
}

func (stmt *TokenBlock) parseInstantiatedFactsBlock() (*[]SpecFactStmt, error) {
	facts := &[]SpecFactStmt{}
	stmt.Header.skip()
	if err := stmt.Header.testAndSkip(KeywordColon); err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	for _, curStmt := range stmt.Body {
		fact, err := curStmt.parseInstantiatedFactStmt()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		*facts = append(*facts, fact)
	}

	return facts, nil
}

func (stmt *TokenBlock) parseDefPropStmt() (*DefPropStmt, error) {
	decl, err := stmt.Header.parsePropDecl()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	ifFacts := &[]FactStmt{}
	thenFacts := &[]FactStmt{}
	if stmt.Header.is(KeywordColon) {
		stmt.Header.skip()
		ifFacts, thenFacts, err = stmt.parseBodyCondFactsThenFacts()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
	}

	return &DefPropStmt{*decl, *ifFacts, *thenFacts}, nil
}

func (stmt *TokenBlock) parseBodyCondFactsThenFacts() (*[]FactStmt, *[]FactStmt, error) {
	ifFacts := &[]FactStmt{}
	thenFacts := &[]FactStmt{}
	var err error = nil

	if len(stmt.Body) == 2 && stmt.Body[0].Header.is(KeywordCond) && stmt.Body[1].Header.is(KeywordThen) {
		stmt.Body[0].Header.skip()
		if err := stmt.Body[0].Header.testAndSkip(KeywordColon); err != nil {
			return nil, nil, err
		}

		ifFacts, err = stmt.Body[0].parseBodyFacts()
		if err != nil {
			return nil, nil, err
		}

		stmt.Body[1].Header.skip()
		if err := stmt.Body[1].Header.testAndSkip(KeywordColon); err != nil {
			return nil, nil, err
		}

		thenFacts, err = stmt.Body[1].parseBodyFacts()
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

func (stmt *TokenBlock) parseDefFnStmt() (*DefFnStmt, error) {
	decl, err := stmt.Header.parseFcFnDecl()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	ifFacts := &[]FactStmt{}
	thenFacts := &[]FactStmt{}

	if stmt.Header.is(KeywordColon) {
		stmt.Header.skip()
		ifFacts, thenFacts, err = stmt.parseBodyCondFactsThenFacts()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
	}

	return &DefFnStmt{decl.name, decl.vars, *ifFacts, *thenFacts}, nil
}

func (stmt *TokenBlock) parseDefObjStmt() (*DefObjStmt, error) {
	err := stmt.Header.skip(KeywordObj)
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	varNames := []string{}

	for !stmt.Header.is(KeywordColon) && !stmt.Header.ExceedEnd() {
		decl, err := stmt.Header.next()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		if stmt.Header.is(KeywordComma) {
			err = stmt.Header.skip(KeywordColon)
			if err != nil {
				return nil, &parseStmtErr{err, *stmt}
			}
		}
		varNames = append(varNames, decl)
	}

	ifFacts := &[]FactStmt{}

	if !stmt.Header.ExceedEnd() && stmt.Header.is(KeywordColon) {
		stmt.Header.skip()
		ifFacts, err = stmt.parseBodyFacts()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
	} else if !stmt.Header.ExceedEnd() {
		return nil, fmt.Errorf("expect ':' or end of block")
	}

	return &DefObjStmt{varNames, *ifFacts}, nil
}

func (stmt *TokenBlock) parseClaimStmt() (ClaimStmt, error) {
	stmt.Header.skip()
	var err error = nil

	if err := stmt.Header.testAndSkip(KeywordColon); err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	toCheck := &[]FactStmt{}
	proof := &[]Stmt{}

	for i := 0; i < len(stmt.Body)-1; i++ {
		if !stmt.Header.is(KeywordProve) && !stmt.Header.is(KeywordProveByContradiction) {
			fact, err := stmt.Body[i].parseFactStmt()
			if err != nil {
				return nil, &parseStmtErr{err, *stmt}
			}
			*toCheck = append(*toCheck, fact)
		}
	}

	isProve := true
	if stmt.Body[len(stmt.Body)-1].Header.is(KeywordProveByContradiction) {
		isProve = false
	} else if !stmt.Body[len(stmt.Body)-1].Header.is(KeywordProve) {
		return nil, fmt.Errorf("expect 'prove' or 'prove_by_contradiction'")
	}
	stmt.Body[len(stmt.Body)-1].Header.skip()

	err = stmt.Body[len(stmt.Body)-1].Header.testAndSkip(KeywordColon)
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	for _, block := range stmt.Body[len(stmt.Body)-1].Body {
		curStmt, err := block.ParseStmt()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		*proof = append(*proof, curStmt)
	}

	if isProve {
		return &ClaimProveStmt{*toCheck, *proof}, nil
	} else {
		return &ClaimProveByContradictStmt{*toCheck, *proof}, nil
	}
}

func (stmt *TokenBlock) parseProveClaimStmt() (*ClaimProveStmt, error) {
	innerStmtArr, err := stmt.parseProveBlock()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}
	return &ClaimProveStmt{[]FactStmt{}, *innerStmtArr}, nil
}

func (stmt *TokenBlock) parseProveBlock() (*[]Stmt, error) {
	stmt.Header.skip(KeywordProve)
	if err := stmt.Header.testAndSkip(KeywordColon); err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	innerStmtArr := []Stmt{}
	for _, innerStmt := range stmt.Body {
		curStmt, err := innerStmt.ParseStmt()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		innerStmtArr = append(innerStmtArr, curStmt)
	}
	return &innerStmtArr, nil
}

func (stmt *TokenBlock) parseKnowStmt() (*KnowStmt, error) {
	stmt.Header.skip(KeywordKnow)

	if !stmt.Header.is(KeywordColon) {
		facts := []FactStmt{}
		fact, err := stmt.parseFactStmt()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		facts = append(facts, fact) // 之所以不能用,让know后面同一行里能有很多很多事实，是因为forall-fact是会换行的
		return &KnowStmt{facts}, nil
	}

	if err := stmt.Header.testAndSkip(KeywordColon); err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	facts, err := stmt.parseBodyFacts()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	return &KnowStmt{*facts}, nil
}

func (stmt *TokenBlock) parseDefExistStmt() (*DefExistStmt, error) {
	decl, err := stmt.Header.parseExistDecl()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	ifFacts := &[]FactStmt{}
	members := &[]InstanceMember{}
	thenFacts := &[]FactStmt{}
	if !stmt.Header.is(KeywordColon) {
		return nil, fmt.Errorf("expected ':‘")
	}

	stmt.Header.skip(KeywordColon)

	for _, curStmt := range stmt.Body {
		if curStmt.Header.is(KeywordCond) {
			ifFacts, err = curStmt.parseBodyFacts()
			if err != nil {
				return nil, &parseStmtErr{err, *stmt}
			}
			continue
		}
		if curStmt.Header.is(KeywordThen) {
			thenFacts, err = curStmt.parseBodyFacts()
			if err != nil {
				return nil, &parseStmtErr{err, *stmt}
			}
			continue
		}
		if curStmt.Header.is(KeywordInstanceMember) {
			for _, memberStmt := range curStmt.Body {
				member, err := memberStmt.parseInstanceMember()
				if err != nil {
					return nil, &parseStmtErr{err, curStmt}
				}
				*members = append(*members, member)
			}

			continue
		}
	}

	return &DefExistStmt{*decl, *ifFacts, *members, *thenFacts}, nil
}

// func (stmt *TokenBlock) parseFcDecls() (*[]fcDecl, error) {
// 	ret := []fcDecl{}

// 	for _, curStmt := range stmt.Body {
// 		cur, err := curStmt.parseFcDecl()
// 		if err != nil {
// 			return nil, &parseStmtErr{err, *stmt}
// 		}
// 		ret = append(ret, cur)
// 	}

// 	return &ret, nil
// }

// func (stmt *TokenBlock) parseFcDecl() (fcDecl, error) {
// 	if stmt.Header.is(Keywords["fn"]) {
// 		return stmt.Header.parseFcFnDecl()
// 	} else if stmt.Header.is(Keywords["var"]) {
// 		// return stmt.Header.parseObjDecl()
// 		panic("unexpected var declaration")
// 	} else if stmt.Header.is(Keywords["prop"]) {
// 		return stmt.Header.parsePropDecl()
// 	}

// 	return nil, fmt.Errorf("expect 'fn', 'var', or 'prop'")
// }

func (stmt *TokenBlock) parseHaveStmt() (*HaveStmt, error) {
	stmt.Header.skip(KeywordHave)
	propStmt, err := stmt.parseFuncPropFactStmt()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	if !stmt.Header.is(KeywordColon) {
		return nil, fmt.Errorf("expected ':'")
	}

	if len(stmt.Body) != 1 {
		return nil, fmt.Errorf("expect one string in members")
	}

	members, err := stmt.Body[0].Header.parseStringArrUntilEnd()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	return &HaveStmt{propStmt, *members}, nil
}

func (stmt *TokenBlock) parseRelationalFactStmt() (SpecFactStmt, error) {
	fc, err := stmt.Header.ParseFc()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	if stmt.Header.strAtCurIndexPlus(0) == KeywordIs {
		return stmt.Header.parseIsExpr(fc)
	}
	// TODO 这里可以考虑和 Relational opt 的处理合并

	opt, err := stmt.Header.next()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	if !isBuiltinRelationalOperator(opt) {
		return nil, &parseStmtErr{err, *stmt}
	}

	fc2, err := stmt.Header.ParseFc()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	params := []Fc{fc, fc2}
	for stmt.Header.is(opt) {
		stmt.Header.skip()
		fc, err := stmt.Header.ParseFc()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		params = append(params, fc)
	}

	return &RelationFactStmt{true, FcAtom{Value: opt}, params}, nil
}

func (stmt *TokenBlock) parseAxiomStmt() (*AxiomStmt, error) {
	stmt.Header.skip(KeywordAxiom)
	decl, err := stmt.parseDefPropExistStmt()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	return &AxiomStmt{decl}, nil
}

func (stmt *TokenBlock) parseThmStmt() (*ThmStmt, error) {
	err := stmt.Header.skip(KeywordThm)
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}
	err = stmt.Header.skip(KeywordColon)
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}
	if !stmt.Header.ExceedEnd() {
		return nil, fmt.Errorf("expect end of line")
	}

	if len(stmt.Body) != 2 {
		return nil, fmt.Errorf("expect two statements in thm")
	}

	decl, err := stmt.Body[0].parseDefPropExistStmt()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	facts, err := stmt.Body[1].parseProveBlock()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	return &ThmStmt{decl, *facts}, nil
}

func (stmt *TokenBlock) parseInlineIfFactStmt() (*WhenCondFactStmt, error) {
	err := stmt.Header.skip(KeywordWhen)
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	condFacts := []FactStmt{}
	for !stmt.Header.is(KeywordLeftCurly) {
		fact, err := stmt.parseInlineFactStmt()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		condFacts = append(condFacts, fact)

		if stmt.Header.is(KeywordComma) {
			stmt.Header.skip()
		}
	}

	thenFacts := []SpecFactStmt{}

	err = stmt.Header.skip(KeywordLeftCurly)
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	for !stmt.Header.is(KeywordRightCurly) {
		fact, err := stmt.parseInstantiatedFactStmt()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		thenFacts = append(thenFacts, fact)

		if stmt.Header.is(KeywordComma) {
			stmt.Header.skip()
		}
	}

	err = stmt.Header.skip(KeywordRightCurly)
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	return &WhenCondFactStmt{condFacts, thenFacts}, nil
}

func (stmt *TokenBlock) parseBlockIfStmt() (*WhenCondFactStmt, error) {
	err := stmt.Header.skip(KeywordWhen)
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}
	err = stmt.Header.skip(KeywordColon)
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}
	if !stmt.Header.ExceedEnd() {
		return nil, fmt.Errorf("expect end of line")
	}

	condFacts := []FactStmt{}
	thenFacts := []SpecFactStmt{}

	for i := 0; i < len(stmt.Body)-1; i++ {
		fact, err := stmt.Body[i].parseInstantiatedFactStmt()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		condFacts = append(condFacts, fact)
	}

	err = stmt.Body[len(stmt.Body)-1].Header.skip(KeywordThen)
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}
	err = stmt.Body[len(stmt.Body)-1].Header.skip(KeywordColon)
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	for i := len(stmt.Body[len(stmt.Body)-1].Body) - 1; i >= 0; i-- {
		fact, err := stmt.Body[len(stmt.Body)-1].Body[i].parseInstantiatedFactStmt()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		thenFacts = append(thenFacts, fact)
	}

	return &WhenCondFactStmt{condFacts, thenFacts}, nil
}
