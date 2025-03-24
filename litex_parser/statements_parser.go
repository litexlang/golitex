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
		ret, err = stmt.parseDefInterfaceStmt()
	case KeywordType:
		ret, err = stmt.parseDefTypeStmt()
	case KeywordSpecProp:
		ret, err = stmt.parseDefConcreteNormalPropStmt()
	case KeywordExistProp:
		ret, err = stmt.parseDefConcreteExistPropStmt()
	case KeywordFn:
		ret, err = stmt.parseDefConcreteFnStmt()
	case KeywordObj:
		ret, err = stmt.parseDefObjStmt()
	case KeywordClaim:
		ret, err = stmt.parseClaimStmt()
	case KeywordProve:
		ret, err = stmt.parseProveClaimStmt()
	case KeywordKnow:
		ret, err = stmt.parseKnowStmt()
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

func (stmt *TokenBlock) parseFactStmt() (FactStmt, error) {
	if stmt.Header.is(KeywordForall) {
		return stmt.parseForallStmt()
	} else if stmt.Header.is(KeywordWhen) {
		return stmt.parseConditionalStmt()
	}
	return stmt.parseSpecFactStmt()
}

func (stmt *TokenBlock) parseSpecFactStmt() (SpecFactStmt, error) {
	isTrue := true
	if stmt.Header.is(KeywordNot) {
		err := stmt.Header.skip(KeywordNot)
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		isTrue = false
	}

	var ret SpecFactStmt
	err := error(nil)
	if stmt.Header.is(KeywordDollar) {
		ret, err = stmt.parseFuncPropFactStmt()
	} else {
		ret, err = stmt.parseRelationalFactStmt()
	}

	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	ret.specFactStmtSetT(isTrue)
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

func (stmt *TokenBlock) parseForallStmt() (ForallStmt, error) {
	err := stmt.Header.skip(KeywordForall)
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	typeParams := &[]string{}
	typeInterfaces := &[]FcAtom{}

	if stmt.Header.is(KeywordLess) {
		stmt.Header.next()
		typeParams, typeInterfaces, err = stmt.Header.parseTypeListInDeclsAndSkipEnd(KeywordGreater)
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
	}

	params, paramTypes, err := stmt.Header.parseParamListInDeclsAndSkipEnd(KeywordColon)
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	condFacts := &[]FactStmt{}
	thenFacts := &[]SpecFactStmt{}

	if stmt.Body[len(stmt.Body)-1].Header.is(KeywordThen) {
		for i := 0; i < len(stmt.Body)-1; i++ {
			curStmt, err := stmt.Body[i].parseFactStmt()
			if err != nil {
				return nil, &parseStmtErr{err, *stmt}
			}
			*condFacts = append(*condFacts, curStmt)
		}
		thenFacts, err = stmt.Body[len(stmt.Body)-1].parseThenBlockSpecFacts()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
	} else {
		for i := 0; i < len(stmt.Body); i++ {
			curStmt, err := stmt.Body[i].parseSpecFactStmt()
			if err != nil {
				return nil, &parseStmtErr{err, *stmt}
			}
			*thenFacts = append(*thenFacts, curStmt)
		}
	}

	if len(*typeParams) > 0 {
		return &GenericForallStmt{*typeParams, *typeInterfaces, *params, *paramTypes, *condFacts, *thenFacts}, nil
	} else {
		return &ConcreteForallStmt{*params, *paramTypes, *condFacts, *thenFacts}, nil
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

func (stmt *TokenBlock) parseThenBlockSpecFacts() (*[]SpecFactStmt, error) {
	facts := &[]SpecFactStmt{}
	stmt.Header.skip() // skip "then"
	if err := stmt.Header.testAndSkip(KeywordColon); err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	for _, curStmt := range stmt.Body {
		fact, err := curStmt.parseSpecFactStmt()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		*facts = append(*facts, fact)
	}

	return facts, nil
}

func (stmt *TokenBlock) parseThenBlockFacts() (*[]FactStmt, error) {
	facts := &[]FactStmt{}
	stmt.Header.skip() // skip "then"
	if err := stmt.Header.testAndSkip(KeywordColon); err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	for _, curStmt := range stmt.Body {
		fact, err := curStmt.parseFactStmt()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		*facts = append(*facts, fact)
	}

	return facts, nil
}

func (stmt *TokenBlock) parseDefConcreteNormalPropStmt() (*DefConcreteNormalPropStmt, error) {
	decl, err := stmt.parseConcreteDefHeader()
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

	return &DefConcreteNormalPropStmt{*decl, *ifFacts, *thenFacts}, nil
}

func (stmt *TokenBlock) parseBodyCondFactsThenFacts() (*[]FactStmt, *[]FactStmt, error) {
	condFacts := &[]FactStmt{}
	thenFacts := &[]FactStmt{}
	err := error(nil)

	if stmt.Body[len(stmt.Body)-1].Header.is(KeywordThen) {
		for i := 0; i < len(stmt.Body)-1; i++ {
			curStmt, err := stmt.Body[i].parseFactStmt()
			if err != nil {
				return nil, nil, &parseStmtErr{err, *stmt}
			}
			*condFacts = append(*condFacts, curStmt)
		}
		thenFacts, err = stmt.Body[len(stmt.Body)-1].parseThenBlockFacts()
		if err != nil {
			return nil, nil, &parseStmtErr{err, *stmt}
		}
	} else {
		for i := 0; i < len(stmt.Body); i++ {
			curStmt, err := stmt.Body[i].parseFactStmt()
			if err != nil {
				return nil, nil, &parseStmtErr{err, *stmt}
			}
			*thenFacts = append(*thenFacts, curStmt)
		}
	}

	return condFacts, thenFacts, nil
}

func (stmt *TokenBlock) parseDefConcreteFnStmt() (*DefConcreteFnStmt, error) {
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

	return &DefConcreteFnStmt{decl.Name, decl.Params, *ifFacts, *thenFacts}, nil
}

func (stmt *TokenBlock) parseDefObjStmt() (*DefObjStmt, error) {
	err := stmt.Header.skip(KeywordObj)
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	paramNames := []string{}

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
		paramNames = append(paramNames, decl)
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

	return &DefObjStmt{paramNames, *ifFacts}, nil
}

func (stmt *TokenBlock) parseClaimStmt() (ClaimStmt, error) {
	stmt.Header.skip()
	err := error(nil)

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

func (stmt *TokenBlock) parseDefConcreteExistPropStmt() (*DefConcreteExistPropStmt, error) {
	decl, err := stmt.parseConcreteDefHeader()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	condFacts := &[]FactStmt{}
	members := &[]DefMember{}
	thenFacts := &[]FactStmt{}
	if !stmt.Header.is(KeywordColon) {
		return nil, fmt.Errorf("expected ':‘")
	}

	stmt.Header.skip(KeywordColon)

	if stmt.Body[len(stmt.Body)-1].Header.is(KeywordThen) {
		for i := 0; i < len(stmt.Body)-1; i++ {
			curStmt, err := stmt.Body[i].parseFactStmt()
			if err != nil {
				return nil, &parseStmtErr{err, *stmt}
			}
			*condFacts = append(*condFacts, curStmt)
		}
		thenFacts, err = stmt.Body[len(stmt.Body)-1].parseThenBlockFacts()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
	} else {
		for i := 0; i < len(stmt.Body); i++ {
			curStmt, err := stmt.Body[i].parseSpecFactStmt()
			if err != nil {
				return nil, &parseStmtErr{err, *stmt}
			}
			*thenFacts = append(*thenFacts, curStmt)
		}
	}

	return &DefConcreteExistPropStmt{*decl, *members, *condFacts, *thenFacts}, nil
}

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

func (stmt *TokenBlock) parseConditionalStmt() (*ConditionalFactStmt, error) {
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
		fact, err := stmt.Body[i].parseSpecFactStmt()
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
		fact, err := stmt.Body[len(stmt.Body)-1].Body[i].parseSpecFactStmt()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		thenFacts = append(thenFacts, fact)
	}

	return &ConditionalFactStmt{condFacts, thenFacts}, nil
}

func (stmt *TokenBlock) parseDefInterfaceStmt() (*DefInterfaceStmt, error) {
	panic("")
}

func (stmt *TokenBlock) parseDefTypeStmt() (*DefTypeStmt, error) {
	panic("")
}

func (stmt *TokenBlock) parseConcreteDefHeader() (*ConcreteDefHeader, error) {
	name, err := stmt.Header.next()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	err = stmt.Header.skip(KeywordLess)
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	params := []string{}
	typeParams := []FcAtom{}

	for !stmt.Header.is(KeywordGreater) {
		param, err := stmt.Header.next()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		params = append(params, param)

		typeParam, err := stmt.Header.parseFcAtom()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}

		typeParams = append(typeParams, typeParam)

		if stmt.Header.is(KeywordComma) {
			stmt.Header.skip()
		}
	}

	err = stmt.Header.skip(KeywordGreater)
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	return &ConcreteDefHeader{name, params, typeParams}, nil
}
