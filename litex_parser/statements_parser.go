package litexparser

import (
	"fmt"
	glob "golitex/litex_global"
)

func (stmt *TokenBlock) ParseTopLevelStmt() (*TopStmt, error) {
	pub := false
	if stmt.Header.is(glob.KeywordPub) {
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
	case glob.KeywordInterface:
		ret, err = stmt.parseDefInterfaceStmt()
	case glob.KeywordType:
		ret, err = stmt.parseDefTypeStmt()
	case glob.KeywordProp:
		ret, err = stmt.parseDefConPropStmt()
	case glob.KeywordExistProp:
		ret, err = stmt.parseDefConExistPropStmt()
	case glob.KeywordFn:
		ret, err = stmt.parseDefConFnStmt()
	case glob.KeywordObj:
		ret, err = stmt.parseDefObjStmt()
	case glob.KeywordClaim:
		ret, err = stmt.parseClaimStmt()
	case glob.KeywordProve:
		ret, err = stmt.parseProveClaimStmt()
	case glob.KeywordKnow:
		ret, err = stmt.parseKnowStmt()
	case glob.KeywordHave:
		ret, err = stmt.parseHaveStmt()
	case glob.KeywordAxiom:
		ret, err = stmt.parseAxiomStmt()
	case glob.KeywordThm:
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
	if stmt.Header.is(glob.KeywordForall) {
		return stmt.parseForallStmt()
	} else if stmt.Header.is(glob.KeywordWhen) {
		return stmt.parseConditionalStmt()
	}
	return stmt.parseSpecFactStmt()
}

func (stmt *TokenBlock) parseSpecFactStmt() (*SpecFactStmt, error) {
	if !stmt.Header.is(glob.KeywordDollar) {
		return stmt.parseRelaFactStmt()
	}

	err := stmt.Header.skip(glob.KeywordDollar)
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	opt, err := stmt.Header.parseFcAtom()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	params := []Fc{}
	err = stmt.Header.skip(glob.KeywordLeftParen)
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	for !stmt.Header.is(glob.KeywordRightParen) {
		param, err := stmt.Header.ParseFc()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		params = append(params, param)
		if stmt.Header.is(glob.KeywordComma) {
			stmt.Header.next()
		}
	}

	err = stmt.Header.skip(glob.KeywordRightParen)
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	return &SpecFactStmt{true, opt, params}, nil
}

func (stmt *TokenBlock) parseForallStmt() (ForallStmt, error) {
	err := stmt.Header.skip(glob.KeywordForall)
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	typeParams := &[]string{}
	typeInterfaces := &[]FcAtom{}

	if stmt.Header.is(glob.KeywordLess) {
		stmt.Header.next()
		typeParams, typeInterfaces, err = stmt.Header.parseTypeListInDeclsAndSkipEnd(glob.KeywordGreater)
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
	}

	params, paramTypes, err := stmt.Header.parseParamListInDeclsAndSkipEnd(glob.KeywordColon)
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	domainFacts := &[]FactStmt{}
	thenFacts := &[]SpecFactStmt{}

	if stmt.Body[len(stmt.Body)-1].Header.is(glob.KeywordThen) {
		for i := 0; i < len(stmt.Body)-1; i++ {
			curStmt, err := stmt.Body[i].parseFactStmt()
			if err != nil {
				return nil, &parseStmtErr{err, *stmt}
			}
			*domainFacts = append(*domainFacts, curStmt)
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
			*thenFacts = append(*thenFacts, *curStmt)
		}
	}

	if len(*typeParams) > 0 {
		return &GenericUniStmt{*typeParams, *typeInterfaces, *params, *paramTypes, *domainFacts, *thenFacts}, nil
	} else {
		return &UniFactStmt{*params, *paramTypes, *domainFacts, *thenFacts}, nil
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
	if err := stmt.Header.testAndSkip(glob.KeywordColon); err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	for _, curStmt := range stmt.Body {
		fact, err := curStmt.parseSpecFactStmt()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		*facts = append(*facts, *fact)
	}

	return facts, nil
}

func (stmt *TokenBlock) parseThenBlockFacts() (*[]FactStmt, error) {
	facts := &[]FactStmt{}
	stmt.Header.skip() // skip "then"
	if err := stmt.Header.testAndSkip(glob.KeywordColon); err != nil {
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

func (stmt *TokenBlock) parseDefConPropStmt() (*DefConPropStmt, error) {
	err := stmt.Header.skip(glob.KeywordProp)
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	decl, err := stmt.parseConDefHeader()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	err = stmt.Header.skip(glob.KeywordColon)
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	condFacts, thenFacts, err := stmt.parseBodyDomThenFacts()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	return &DefConPropStmt{*decl, *condFacts, *thenFacts}, nil
}

// func (stmt *TokenBlock) parseBodyWhenFactsThenFacts() (*[]FactStmt, *[]FactStmt, error) {
// 	condFacts := &[]FactStmt{}
// 	thenFacts := &[]FactStmt{}
// 	err := error(nil)

// 	if stmt.Body[len(stmt.Body)-1].Header.is(glob.KeywordThen) {
// 		for i := 0; i < len(stmt.Body)-1; i++ {
// 			curStmt, err := stmt.Body[i].parseFactStmt()
// 			if err != nil {
// 				return nil, nil, &parseStmtErr{err, *stmt}
// 			}
// 			*condFacts = append(*condFacts, curStmt)
// 		}
// 		thenFacts, err = stmt.Body[len(stmt.Body)-1].parseThenBlockFacts()
// 		if err != nil {
// 			return nil, nil, &parseStmtErr{err, *stmt}
// 		}
// 	} else if stmt.Body[0].Header.is(glob.KeywordWhen) {
// 		err = stmt.Body[0].Header.skip(glob.KeywordWhen)
// 		if err != nil {
// 			return nil, nil, &parseStmtErr{err, *stmt}
// 		}
// 		err = stmt.Body[0].Header.skip(glob.KeywordColon)
// 		if err != nil {
// 			return nil, nil, &parseStmtErr{err, *stmt}
// 		}

// 		for _, condFact := range stmt.Body[0].Body {
// 			curStmt, err := condFact.parseFactStmt()
// 			if err != nil {
// 				return nil, nil, &parseStmtErr{err, *stmt}
// 			}
// 			*condFacts = append(*condFacts, curStmt)
// 		}

// 		for i := 1; i < len(stmt.Body); i++ {
// 			curStmt, err := stmt.Body[i].parseFactStmt()
// 			if err != nil {
// 				return nil, nil, &parseStmtErr{err, *stmt}
// 			}
// 			*thenFacts = append(*thenFacts, curStmt)
// 		}
// 	} else {
// 		for i := 0; i < len(stmt.Body); i++ {
// 			curStmt, err := stmt.Body[i].parseFactStmt()
// 			if err != nil {
// 				return nil, nil, &parseStmtErr{err, *stmt}
// 			}
// 			*thenFacts = append(*thenFacts, curStmt)
// 		}
// 	}

// 	return condFacts, thenFacts, nil
// }

func (stmt *TokenBlock) parseBodyDomThenFacts() (*[]FactStmt, *[]FactStmt, error) {
	condFacts := &[]FactStmt{}
	thenFacts := &[]FactStmt{}
	err := error(nil)

	if stmt.Body[len(stmt.Body)-1].Header.is(glob.KeywordThen) {
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
	} else if stmt.Body[0].Header.is(glob.KeywordDom) {
		err = stmt.Body[0].Header.skip(glob.KeywordDom)
		if err != nil {
			return nil, nil, &parseStmtErr{err, *stmt}
		}
		err = stmt.Body[0].Header.skip(glob.KeywordColon)
		if err != nil {
			return nil, nil, &parseStmtErr{err, *stmt}
		}

		for _, condFact := range stmt.Body[0].Body {
			curStmt, err := condFact.parseFactStmt()
			if err != nil {
				return nil, nil, &parseStmtErr{err, *stmt}
			}
			*condFacts = append(*condFacts, curStmt)
		}

		for i := 1; i < len(stmt.Body); i++ {
			curStmt, err := stmt.Body[i].parseFactStmt()
			if err != nil {
				return nil, nil, &parseStmtErr{err, *stmt}
			}
			*thenFacts = append(*thenFacts, curStmt)
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

func (stmt *TokenBlock) parseDefConFnStmt() (*DefConFnStmt, error) {
	err := stmt.Header.skip(glob.KeywordFn)
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	decl, err := stmt.parseConDefHeader()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	retType, err := stmt.Header.parseFcAtom()
	if err != nil {
		return nil, err
	}

	ifFacts := &[]FactStmt{}
	thenFacts := &[]FactStmt{}

	if stmt.Header.is(glob.KeywordColon) {
		stmt.Header.skip()
		ifFacts, thenFacts, err = stmt.parseBodyDomThenFacts()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
	}

	return &DefConFnStmt{*decl, retType, *ifFacts, *thenFacts}, nil
}

func (stmt *TokenBlock) parseDefObjStmt() (*DefObjStmt, error) {
	err := stmt.Header.skip(glob.KeywordObj)
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	paramNames := []string{}

	for !stmt.Header.is(glob.KeywordColon) && !stmt.Header.ExceedEnd() {
		decl, err := stmt.Header.next()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		if stmt.Header.is(glob.KeywordComma) {
			err = stmt.Header.skip(glob.KeywordColon)
			if err != nil {
				return nil, &parseStmtErr{err, *stmt}
			}
		}
		paramNames = append(paramNames, decl)
	}

	ifFacts := &[]FactStmt{}

	if !stmt.Header.ExceedEnd() && stmt.Header.is(glob.KeywordColon) {
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

	if err := stmt.Header.testAndSkip(glob.KeywordColon); err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	toCheck := &[]FactStmt{}
	proof := &[]Stmt{}

	for i := 0; i < len(stmt.Body)-1; i++ {
		if !stmt.Header.is(glob.KeywordProve) && !stmt.Header.is(glob.KeywordProveByContradiction) {
			fact, err := stmt.Body[i].parseFactStmt()
			if err != nil {
				return nil, &parseStmtErr{err, *stmt}
			}
			*toCheck = append(*toCheck, fact)
		}
	}

	isProve := true
	if stmt.Body[len(stmt.Body)-1].Header.is(glob.KeywordProveByContradiction) {
		isProve = false
	} else if !stmt.Body[len(stmt.Body)-1].Header.is(glob.KeywordProve) {
		return nil, fmt.Errorf("expect 'prove' or 'prove_by_contradiction'")
	}
	stmt.Body[len(stmt.Body)-1].Header.skip()

	err = stmt.Body[len(stmt.Body)-1].Header.testAndSkip(glob.KeywordColon)
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
	stmt.Header.skip(glob.KeywordProve)
	if err := stmt.Header.testAndSkip(glob.KeywordColon); err != nil {
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
	stmt.Header.skip(glob.KeywordKnow)

	if !stmt.Header.is(glob.KeywordColon) {
		facts := []FactStmt{}
		fact, err := stmt.parseFactStmt()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		facts = append(facts, fact) // 之所以不能用,让know后面同一行里能有很多很多事实，是因为forall-fact是会换行的
		return &KnowStmt{facts}, nil
	}

	if err := stmt.Header.testAndSkip(glob.KeywordColon); err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	facts, err := stmt.parseBodyFacts()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	return &KnowStmt{*facts}, nil
}

func (stmt *TokenBlock) parseDefConExistPropStmt() (*DefConExistPropStmt, error) {
	err := stmt.Header.skip(glob.KeywordExistProp)
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	decl, err := stmt.parseConDefHeader()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	existObjOrFn := []string{}
	existObjOrFnTypes := []FcAtom{}

	for !stmt.Header.is(glob.KeywordColon) && !stmt.Header.ExceedEnd() {
		decl, err := stmt.Header.next()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		tp, err := stmt.Header.parseFcAtom()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		existObjOrFn = append(existObjOrFn, decl)
		existObjOrFnTypes = append(existObjOrFnTypes, tp)
		if stmt.Header.is(glob.KeywordComma) {
			stmt.Header.skip()
		}
	}

	err = stmt.Header.skip(glob.KeywordColon)
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	condFacts, thenFacts, err := stmt.parseBodyDomThenFacts()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	return &DefConExistPropStmt{*decl, existObjOrFn, existObjOrFnTypes, *condFacts, *thenFacts}, nil
}

func (stmt *TokenBlock) parseHaveStmt() (*HaveStmt, error) {
	stmt.Header.skip(glob.KeywordHave)
	propStmt, err := stmt.parseSpecFactStmt()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	if !stmt.Header.is(glob.KeywordColon) {
		return nil, fmt.Errorf("expected ':'")
	}

	if len(stmt.Body) != 1 {
		return nil, fmt.Errorf("expect one string in members")
	}

	members, err := stmt.Body[0].Header.parseStringArrUntilEnd()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	return &HaveStmt{*propStmt, *members}, nil
}

func (stmt *TokenBlock) parseRelaFactStmt() (*SpecFactStmt, error) {
	fc, err := stmt.Header.ParseFc()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	if stmt.Header.strAtCurIndexPlus(0) == glob.KeywordIs {
		return stmt.Header.parseIsExpr(fc)
	}

	opt, err := stmt.Header.next()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	if !glob.IsBuiltinRelaOpt(opt) {
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

	// if opt != "=" {
	return &SpecFactStmt{true, FcAtom{OptName: opt}, params}, nil
	// } else {
	// 	return &RelaFactStmt{false, FcAtom{OptName: opt}, params}, nil
	// }
	// return &RelaFactStmt{true, FcAtom{OptName: opt}, params}, nil
}

func (stmt *TokenBlock) parseAxiomStmt() (*AxiomStmt, error) {
	stmt.Header.skip(glob.KeywordAxiom)
	decl, err := stmt.parseDefPropExistStmt()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	return &AxiomStmt{decl}, nil
}

func (stmt *TokenBlock) parseThmStmt() (*ThmStmt, error) {
	err := stmt.Header.skip(glob.KeywordThm)
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}
	err = stmt.Header.skip(glob.KeywordColon)
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

func (stmt *TokenBlock) parseConditionalStmt() (*CondFactStmt, error) {
	err := stmt.Header.skip(glob.KeywordWhen)
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}
	err = stmt.Header.skip(glob.KeywordColon)
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

	err = stmt.Body[len(stmt.Body)-1].Header.skip(glob.KeywordThen)
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}
	err = stmt.Body[len(stmt.Body)-1].Header.skip(glob.KeywordColon)
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	for i := len(stmt.Body[len(stmt.Body)-1].Body) - 1; i >= 0; i-- {
		fact, err := stmt.Body[len(stmt.Body)-1].Body[i].parseSpecFactStmt()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		thenFacts = append(thenFacts, *fact)
	}

	return &CondFactStmt{condFacts, thenFacts}, nil
}

func (stmt *TokenBlock) parseDefInterfaceStmt() (*DefInterfaceStmt, error) {
	panic("")
}

func (stmt *TokenBlock) parseDefTypeStmt() (*DefTypeStmt, error) {
	panic("")
}

func (stmt *TokenBlock) parseConDefHeader() (*ConDefHeader, error) {
	name, err := stmt.Header.next()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	err = stmt.Header.skip(glob.KeywordLeftParen)
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	params := []string{}
	typeParams := []FcAtom{}

	for !stmt.Header.is(glob.KeywordRightParen) {
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

		if stmt.Header.is(glob.KeywordComma) {
			stmt.Header.skip()
		}
	}

	err = stmt.Header.skip(glob.KeywordRightParen)
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	return &ConDefHeader{name, params, typeParams}, nil
}
