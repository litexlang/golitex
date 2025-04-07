package litexparser

import (
	"fmt"
	ast "golitex/litex_ast"
	glob "golitex/litex_global"
)

func (stmt *TokenBlock) ParseTopLevelStmt() (*ast.TopStmt, error) {
	pub := false
	if stmt.Header.is(glob.KeywordPub) {
		stmt.Header.skip()
		pub = true
	}

	ret, err := stmt.ParseStmt()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	// return &ast.TopStmt{ret, pub}, nil
	return ast.MakeTopStmt(ret, pub), nil
}

func (stmt *TokenBlock) ParseStmt() (ast.Stmt, error) {
	cur, err := stmt.Header.currentToken()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	var ret ast.Stmt
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

func (stmt *TokenBlock) parseFactStmt() (ast.FactStmt, error) {
	if stmt.Header.is(glob.KeywordForall) {
		return stmt.parseForallStmt()
	} else if stmt.Header.is(glob.KeywordWhen) {
		return stmt.parseConditionalStmt()
	}
	return stmt.parseSpecFactStmt()
}

func (stmt *TokenBlock) parseSpecFactStmt() (*ast.SpecFactStmt, error) {
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

	params := []ast.Fc{}
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

	// return &ast.SpecFactStmt{true, opt, params}, nil
	return ast.MakeSpecFactStmt(true, opt, params), nil
}

func (stmt *TokenBlock) parseForallStmt() (ast.ForallStmt, error) {
	err := stmt.Header.skip(glob.KeywordForall)
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	typeParams := []string{}
	typeInterfaces := []*ast.FcAtom{}

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

	domainFacts := []ast.FactStmt{}
	thenFacts := []*ast.SpecFactStmt{}

	if stmt.Body[len(stmt.Body)-1].Header.is(glob.KeywordThen) {
		for i := 0; i < len(stmt.Body)-1; i++ {
			curStmt, err := stmt.Body[i].parseFactStmt()
			if err != nil {
				return nil, &parseStmtErr{err, *stmt}
			}
			domainFacts = append(domainFacts, curStmt)
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
			thenFacts = append(thenFacts, curStmt)
		}
	}

	if len(typeParams) > 0 {
		// return &ast.GenericUniStmt{typeParams, typeInterfaces, params, paramTypes, domainFacts, thenFacts}, nil
		return ast.MakeGenericUniStmt(typeParams, typeInterfaces, params, paramTypes, domainFacts, thenFacts), nil
	} else {
		// return &ast.UniFactStmt{params, paramTypes, domainFacts, thenFacts}, nil
		return ast.MakeUniFactStmt(params, paramTypes, domainFacts, thenFacts), nil
	}

}

func (stmt *TokenBlock) parseBodyFacts() ([]ast.FactStmt, error) {
	facts := []ast.FactStmt{}
	for _, f := range stmt.Body {
		fact, err := f.parseFactStmt()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		facts = append(facts, fact)
	}

	return facts, nil
}

func (stmt *TokenBlock) parseThenBlockSpecFacts() ([]*ast.SpecFactStmt, error) {
	facts := []*ast.SpecFactStmt{}
	stmt.Header.skip() // skip "then"
	if err := stmt.Header.testAndSkip(glob.KeywordColon); err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	for _, curStmt := range stmt.Body {
		fact, err := curStmt.parseSpecFactStmt()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		facts = append(facts, fact)
	}

	return facts, nil
}

func (stmt *TokenBlock) parseBlockHeaderBodyFacts(kw string) ([]ast.FactStmt, error) {
	facts := []ast.FactStmt{}
	stmt.Header.skip(kw)
	if err := stmt.Header.testAndSkip(glob.KeywordColon); err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	for _, curStmt := range stmt.Body {
		fact, err := curStmt.parseFactStmt()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		facts = append(facts, fact)
	}

	return facts, nil
}

func (stmt *TokenBlock) parseDefConPropStmt() (*ast.DefConPropStmt, error) {
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

	domFacts, iffFacts, err := stmt.parseBodyFactSectionSpecFactSection(glob.KeywordIff)
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	// return &ast.DefConPropStmt{*decl, domFacts, iffFacts}, nil
	return ast.MakeDefConPropStmt(*decl, domFacts, iffFacts), nil
}

func (stmt *TokenBlock) parseBodyTwoFactSections(kw string) ([]ast.FactStmt, []ast.FactStmt, error) {
	section1Facts := []ast.FactStmt{}
	section2Facts := []ast.FactStmt{}
	err := error(nil)

	if stmt.Body[len(stmt.Body)-1].Header.is(kw) {
		for i := 0; i < len(stmt.Body)-1; i++ {
			curStmt, err := stmt.Body[i].parseFactStmt()
			if err != nil {
				return nil, nil, &parseStmtErr{err, *stmt}
			}
			section1Facts = append(section1Facts, curStmt)
		}
		section2Facts, err = stmt.Body[len(stmt.Body)-1].parseBlockHeaderBodyFacts(kw)
		if err != nil {
			return nil, nil, &parseStmtErr{err, *stmt}
		}
	} else {
		for i := 0; i < len(stmt.Body); i++ {
			curStmt, err := stmt.Body[i].parseFactStmt()
			if err != nil {
				return nil, nil, &parseStmtErr{err, *stmt}
			}
			section2Facts = append(section2Facts, curStmt)
		}
	}

	return section1Facts, section2Facts, nil
}

func (stmt *TokenBlock) parseDefConFnStmt() (*ast.DefConFnStmt, error) {
	err := stmt.Header.skip(glob.KeywordFn)
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	decl, err := stmt.parseConDefHeader()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	retType, err := stmt.Header.ParseFc()
	if err != nil {
		return nil, err
	}

	domFacts := []ast.FactStmt{}
	thenFacts := []*ast.SpecFactStmt{}

	if stmt.Header.is(glob.KeywordColon) {
		stmt.Header.skip()
		domFacts, thenFacts, err = stmt.parseBodyFactSectionSpecFactSection(glob.KeywordThen)
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
	}

	// return &ast.DefConFnStmt{*decl, retType, domFacts, thenFacts}, nil
	return ast.MakeDefConFnStmt(*decl, retType, domFacts, thenFacts), nil
}

func (stmt *TokenBlock) parseDefObjStmt() (*ast.DefObjStmt, error) {
	err := stmt.Header.skip(glob.KeywordObj)
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	objNames := []string{}
	objSets := []ast.Fc{}

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
		objNames = append(objNames, decl)
		tp, err := stmt.Header.ParseFc()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		objSets = append(objSets, tp)
	}

	facts := []ast.FactStmt{}

	if !stmt.Header.ExceedEnd() && stmt.Header.is(glob.KeywordColon) {
		stmt.Header.skip()
		facts, err = stmt.parseBodyFacts()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
	} else if !stmt.Header.ExceedEnd() {
		return nil, fmt.Errorf("expect ':' or end of block")
	}

	// return &ast.DefObjStmt{objNames, objSets, facts}, nil
	return ast.MakeDefObjStmt(objNames, objSets, facts), nil
}

func (stmt *TokenBlock) parseClaimStmt() (ast.ClaimStmt, error) {
	stmt.Header.skip()
	err := error(nil)

	if err := stmt.Header.testAndSkip(glob.KeywordColon); err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	toCheck := &[]ast.FactStmt{}
	proof := &[]ast.Stmt{}

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
		// return &ast.ClaimProveStmt{*toCheck, *proof}, nil
		return ast.MakeClaimProveStmt(*toCheck, *proof), nil
	} else {
		// return &ast.ClaimProveByContradictStmt{*toCheck, *proof}, nil
		return ast.MakeClaimProveByContradictStmt(*toCheck, *proof), nil
	}
}

func (stmt *TokenBlock) parseProveClaimStmt() (*ast.ClaimProveStmt, error) {
	innerStmtArr, err := stmt.parseProveBlock()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}
	// return &ast.ClaimProveStmt{[]ast.FactStmt{}, innerStmtArr}, nil
	return ast.MakeClaimProveStmt([]ast.FactStmt{}, innerStmtArr), nil
}

func (stmt *TokenBlock) parseProveBlock() ([]ast.Stmt, error) {
	stmt.Header.skip(glob.KeywordProve)
	if err := stmt.Header.testAndSkip(glob.KeywordColon); err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	innerStmtArr := []ast.Stmt{}
	for _, innerStmt := range stmt.Body {
		curStmt, err := innerStmt.ParseStmt()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		innerStmtArr = append(innerStmtArr, curStmt)
	}
	return innerStmtArr, nil
}

func (stmt *TokenBlock) parseKnowStmt() (*ast.KnowStmt, error) {
	stmt.Header.skip(glob.KeywordKnow)

	if !stmt.Header.is(glob.KeywordColon) {
		facts := []ast.FactStmt{}
		fact, err := stmt.parseFactStmt()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		facts = append(facts, fact) // 之所以不能用,让know后面同一行里能有很多很多事实，是因为forall-fact是会换行的
		// return &ast.KnowStmt{facts}, nil
		return ast.MakeKnowStmt(facts), nil
	}

	if err := stmt.Header.testAndSkip(glob.KeywordColon); err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	facts, err := stmt.parseBodyFacts()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	// return &ast.KnowStmt{facts}, nil
	return ast.MakeKnowStmt(facts), nil
}

func (stmt *TokenBlock) parseDefConExistPropStmt() (*ast.DefConExistPropStmt, error) {
	err := stmt.Header.skip(glob.KeywordExistProp)
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	decl, err := stmt.parseConDefHeader()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	existObjOrFn := []string{}
	existObjOrFnTypes := []*ast.FcAtom{}

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
		existObjOrFnTypes = append(existObjOrFnTypes, &tp)
		if stmt.Header.is(glob.KeywordComma) {
			stmt.Header.skip()
		}
	}

	err = stmt.Header.skip(glob.KeywordColon)
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	domFacts, thenFacts, err := stmt.parseBodyTwoFactSections(glob.KeywordIff)
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	// return &ast.DefConExistPropStmt{*decl, existObjOrFn, existObjOrFnTypes, domFacts, thenFacts}, nil
	return ast.MakeDefConExistPropStmt(*decl, existObjOrFn, existObjOrFnTypes, domFacts, thenFacts), nil
}

func (stmt *TokenBlock) parseHaveStmt() (*ast.HaveStmt, error) {
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

	// return &ast.HaveStmt{*propStmt, members}, nil
	return ast.MakeHaveStmt(*propStmt, members), nil
}

func (stmt *TokenBlock) parseRelaFactStmt() (*ast.SpecFactStmt, error) {
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

	if !glob.IsBuiltinRelaProp(opt) {
		return nil, &parseStmtErr{err, *stmt}
	}

	fc2, err := stmt.Header.ParseFc()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	params := []ast.Fc{fc, fc2}
	for stmt.Header.is(opt) {
		stmt.Header.skip()
		fc, err := stmt.Header.ParseFc()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		params = append(params, fc)
	}

	// return &ast.SpecFactStmt{true, ast.FcAtom{Value: opt}, params}, nil
	return ast.MakeSpecFactStmt(true, ast.FcAtom{Value: opt}, params), nil
}

func (stmt *TokenBlock) parseAxiomStmt() (*ast.AxiomStmt, error) {
	stmt.Header.skip(glob.KeywordAxiom)
	decl, err := stmt.parseDefPropExistStmt()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	// return &ast.AxiomStmt{decl}, nil
	return ast.MakeAxiomStmt(decl), nil
}

func (stmt *TokenBlock) parseThmStmt() (*ast.ThmStmt, error) {
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

	// return &ast.ThmStmt{decl, facts}, nil
	return ast.MakeThmStmt(decl, facts), nil
}

func (stmt *TokenBlock) parseConditionalStmt() (*ast.CondFactStmt, error) {
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

	condFacts := []ast.FactStmt{}
	thenFacts := []*ast.SpecFactStmt{}

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
		thenFacts = append(thenFacts, fact)
	}

	// return &ast.CondFactStmt{condFacts, thenFacts}, nil
	return ast.MakeCondFactStmt(condFacts, thenFacts), nil
}

func (stmt *TokenBlock) parseDefInterfaceStmt() (*ast.DefInterfaceStmt, error) {
	panic("")
}

func (stmt *TokenBlock) parseDefTypeStmt() (*ast.DefTypeStmt, error) {
	panic("")
}

func (stmt *TokenBlock) parseConDefHeader() (*ast.ConDefHeader, error) {
	name, err := stmt.Header.next()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	err = stmt.Header.skip(glob.KeywordLeftParen)
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	params := []string{}
	typeParams := []ast.Fc{}

	for !stmt.Header.is(glob.KeywordRightParen) {
		param, err := stmt.Header.next()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		params = append(params, param)

		typeParam, err := stmt.Header.ParseFc()
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

	// return &ast.ConDefHeader{name, params, typeParams}, nil
	return ast.MakeConDefHeader(name, params, typeParams), nil
}

func (stmt *TokenBlock) parseBodyFactSectionSpecFactSection(kw string) ([]ast.FactStmt, []*ast.SpecFactStmt, error) {
	section1Facts := []ast.FactStmt{}
	section2SpecFacts := []*ast.SpecFactStmt{}
	err := error(nil)

	if stmt.Body[len(stmt.Body)-1].Header.is(kw) {
		for i := 0; i < len(stmt.Body)-1; i++ {
			curStmt, err := stmt.Body[i].parseFactStmt()
			if err != nil {
				return nil, nil, &parseStmtErr{err, *stmt}
			}
			section1Facts = append(section1Facts, curStmt)
		}
		section2SpecFacts, err = stmt.Body[len(stmt.Body)-1].parseThenBlockSpecFacts()
		if err != nil {
			return nil, nil, &parseStmtErr{err, *stmt}
		}
	} else {
		for i := 0; i < len(stmt.Body); i++ {
			curStmt, err := stmt.Body[i].parseSpecFactStmt()
			if err != nil {
				return nil, nil, &parseStmtErr{err, *stmt}
			}
			section2SpecFacts = append(section2SpecFacts, curStmt)
		}
	}

	return section1Facts, section2SpecFacts, nil
}
