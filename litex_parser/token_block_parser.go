package litex_parser

import (
	"fmt"
	ast "golitex/litex_ast"
	glob "golitex/litex_global"
	"strings"
)

type nameDepthMap map[string]int

func (stmt *tokenBlock) TopStmt() (*ast.TopStmt, error) {
	pub := false
	if stmt.header.is(glob.KeywordPub) {
		stmt.header.skip()
		pub = true
	}

	ret, err := stmt.Stmt()
	if err != nil {
		return nil, &parseTimeErr{err, *stmt}
	}

	return ast.NewTopStmt(ret, pub), nil
}

func (stmt *tokenBlock) Stmt() (ast.Stmt, error) {
	cur, err := stmt.header.currentToken()
	if err != nil {
		return nil, &parseTimeErr{err, *stmt}
	}

	var ret ast.Stmt
	switch cur {
	case glob.KeywordInterface:
		ret, err = stmt.defInterfaceStmt()
	case glob.KeywordType:
		ret, err = stmt.defTypeStmt()
	case glob.KeywordProp:
		ret, err = stmt.defConPropStmt()
	case glob.KeywordExistProp:
		ret, err = stmt.defConExistPropStmt()
	case glob.KeywordFn:
		ret, err = stmt.defConFnStmt()
	case glob.KeywordObj:
		ret, err = stmt.defObjStmt()
	case glob.KeywordClaim:
		ret, err = stmt.claimStmt()
	case glob.KeywordProve:
		ret, err = stmt.proveClaimStmt()
	case glob.KeywordKnow:
		ret, err = stmt.knowStmt()
	case glob.KeywordHave:
		ret, err = stmt.haveStmt()
	case glob.KeywordAxiom:
		ret, err = stmt.axiomStmt()
	case glob.KeywordThm:
		ret, err = stmt.thmStmt()
	default:
		ret, err = stmt.factStmt(nameDepthMap{}, true)
	}

	if err != nil {
		return nil, &parseTimeErr{err, *stmt}
	}

	if !stmt.header.ExceedEnd() {
		return nil, &parseTimeErr{err, *stmt}
	}

	return ret, nil
}

func (stmt *tokenBlock) factStmt(nameDepths nameDepthMap, uniFactDom bool) (ast.FactStmt, error) {
	if stmt.header.is(glob.KeywordForall) {
		return stmt.uniFactStmt(nameDepths, uniFactDom)
	} else if stmt.header.is(glob.KeywordWhen) {
		return stmt.condFactStmt(nameDepths)
	}
	return stmt.specFactStmt(nameDepths)
}

func (stmt *tokenBlock) specFactStmt(nameDepths nameDepthMap) (*ast.SpecFactStmt, error) {
	// if !stmt.header.is(glob.KeySymbolDollar) {
	// 	return stmt.relaFactStmt()
	// }

	// err := stmt.header.skip(glob.KeySymbolDollar)
	// if err != nil {
	// 	return nil, &parseTimeErr{err, *stmt}
	// }

	isTrue := true
	if stmt.header.is(glob.KeywordNot) {
		stmt.header.skip(glob.KeywordNot)
		isTrue = false
	}

	ok, err := stmt.isSpecFactNotRelaFact()
	if err != nil {
		return nil, err
	}
	if !ok {
		return stmt.relaFactStmt(nameDepths)
	}

	propName, err := stmt.header.rawFcAtom()
	if err != nil {
		return nil, &parseTimeErr{err, *stmt}
	}
	propName = *ast.AddUniPrefixToFcAtom(&propName, nameDepths)

	params := []ast.Fc{}
	err = stmt.header.skip(glob.KeySymbolLeftBrace)
	if err != nil {
		return nil, &parseTimeErr{err, *stmt}
	}

	for !stmt.header.is(glob.KeySymbolRightBrace) {
		param, err := stmt.header.rawFc()
		if err != nil {
			return nil, &parseTimeErr{err, *stmt}
		}

		param, err = ast.AddUniPrefixToFc(param, nameDepths)
		if err != nil {
			return nil, &parseTimeErr{err, *stmt}
		}

		params = append(params, param)
		if stmt.header.is(glob.KeySymbolComma) {
			stmt.header.next()
		}
	}

	err = stmt.header.skip(glob.KeySymbolRightBrace)
	if err != nil {
		return nil, &parseTimeErr{err, *stmt}
	}

	return ast.NewSpecFactStmt(isTrue, propName, params), nil
}

func (stmt *tokenBlock) uniFactStmt(nameDepths nameDepthMap, maxAllowedNestedForall bool) (ast.UniFactStmt, error) {
	err := stmt.header.skip(glob.KeywordForall)
	if err != nil {
		return nil, &parseTimeErr{err, *stmt}
	}

	typeParams := []string{}
	typeInterfaces := []*ast.FcAtom{}

	if stmt.header.is(glob.KeySymbolLess) {
		stmt.header.next()
		typeParams, typeInterfaces, err = stmt.header.typeListInDeclsAndSkipEnd(glob.KeySymbolGreater)
		if err != nil {
			return nil, &parseTimeErr{err, *stmt}
		}
	}

	params, paramTypes, err := stmt.header.paramSliceInDeclHeadAndSkipEnd(glob.KeySymbolColon)
	if err != nil {
		return nil, &parseTimeErr{err, *stmt}
	}

	newUniParams := nameDepthMap{}
	for key := range nameDepths {
		newUniParams[key] = nameDepths[key]
	}

	for i := range params {
		prefixNum, declared := nameDepths[params[i]]
		if !declared {
			newUniParams[params[i]] = 1
			params[i] = fmt.Sprintf("%s%s", glob.UniParamPrefix, params[i])
		} else {
			newUniParams[params[i]] = prefixNum + 1
			params[i] = strings.Repeat(glob.UniParamPrefix, prefixNum+1) + params[i]
		}
	}

	domainFacts := []ast.FactStmt{}
	thenFacts := []*ast.SpecFactStmt{}

	if stmt.body[len(stmt.body)-1].header.is(glob.KeywordThen) {
		for i := 0; i < len(stmt.body)-1; i++ {
			if maxAllowedNestedForall {
				curStmt, err := stmt.body[i].factStmt(newUniParams, false)
				if err != nil {
					return nil, &parseTimeErr{err, *stmt}
				}
				domainFacts = append(domainFacts, curStmt)
			} else {
				curStmt, err := stmt.body[i].specFactStmt(newUniParams)
				if err != nil {
					return nil, uniDomFactMoreThanOneLayerUniFactErrMsg(err, stmt)
				}
				domainFacts = append(domainFacts, curStmt)
			}
		}
		thenFacts, err = stmt.body[len(stmt.body)-1].thenBlockSpecFacts(newUniParams)
		if err != nil {
			return nil, &parseTimeErr{err, *stmt}
		}
	} else {
		for i := 0; i < len(stmt.body); i++ {
			// 这里要么是直接parse Spec Fact ，要么是parseFact，然后(*type)成spec。前者好处是，就应该这么干；后者好处是，如果你输入了forall，那我报错可以直接指出问题
			// Method1
			curStmt, err := stmt.body[i].specFactStmt(newUniParams)
			if err != nil {
				return nil, thenFactMustSpecMsg(&stmt.body[i], err)
			}

			thenFacts = append(thenFacts, curStmt)
		}
	}

	if len(typeParams) > 0 {
		return ast.NewGenericUniStmt(typeParams, typeInterfaces, params, paramTypes, domainFacts, thenFacts), nil
	} else {
		return ast.NewUniFactStmt(params, paramTypes, domainFacts, thenFacts), nil
	}
}

func (stmt *tokenBlock) bodyFacts(nameDepths nameDepthMap) ([]ast.FactStmt, error) {
	facts := []ast.FactStmt{}
	for _, f := range stmt.body {
		fact, err := f.factStmt(nameDepths, true)
		if err != nil {
			return nil, &parseTimeErr{err, *stmt}
		}
		facts = append(facts, fact)
	}

	return facts, nil
}

func (stmt *tokenBlock) thenBlockSpecFacts(nameDepths nameDepthMap) ([]*ast.SpecFactStmt, error) {
	facts := []*ast.SpecFactStmt{}
	stmt.header.skip() // skip "then"
	if err := stmt.header.testAndSkip(glob.KeySymbolColon); err != nil {
		return nil, &parseTimeErr{err, *stmt}
	}

	for _, curStmt := range stmt.body {
		fact, err := curStmt.specFactStmt(nameDepths)
		if err != nil {
			return nil, thenFactMustSpecMsg(&curStmt, err)
		}

		facts = append(facts, fact)
	}

	return facts, nil
}

func (stmt *tokenBlock) blockHeaderBodyFacts(kw string, nameDepths nameDepthMap) ([]ast.FactStmt, error) {
	facts := []ast.FactStmt{}
	stmt.header.skip(kw)
	if err := stmt.header.testAndSkip(glob.KeySymbolColon); err != nil {
		return nil, &parseTimeErr{err, *stmt}
	}

	for _, curStmt := range stmt.body {
		fact, err := curStmt.factStmt(nameDepths, true)
		if err != nil {
			return nil, &parseTimeErr{err, *stmt}
		}
		facts = append(facts, fact)
	}

	return facts, nil
}

func (stmt *tokenBlock) defConPropStmt() (*ast.DefConPropStmt, error) {
	err := stmt.header.skip(glob.KeywordProp)
	if err != nil {
		return nil, &parseTimeErr{err, *stmt}
	}

	declHeader, nameDepths, err := stmt.conDefHeader()
	if err != nil {
		return nil, &parseTimeErr{err, *stmt}
	}

	err = stmt.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, &parseTimeErr{err, *stmt}
	}

	domFacts, iffFacts, err := stmt.bodyFactSectionSpecFactSection(glob.KeywordIff, nameDepths)
	if err != nil {
		return nil, &parseTimeErr{err, *stmt}
	}

	return ast.NewDefConPropStmt(*declHeader, domFacts, iffFacts), nil
}

func (stmt *tokenBlock) bodyTwoFactSections(kw string, nameDepths nameDepthMap) ([]ast.FactStmt, []ast.FactStmt, error) {
	section1Facts := []ast.FactStmt{}
	section2Facts := []ast.FactStmt{}
	err := error(nil)

	if stmt.body[len(stmt.body)-1].header.is(kw) {
		for i := 0; i < len(stmt.body)-1; i++ {
			curStmt, err := stmt.body[i].factStmt(nameDepths, true)
			if err != nil {
				return nil, nil, &parseTimeErr{err, *stmt}
			}
			section1Facts = append(section1Facts, curStmt)
		}
		section2Facts, err = stmt.body[len(stmt.body)-1].blockHeaderBodyFacts(kw, nameDepths)
		if err != nil {
			return nil, nil, &parseTimeErr{err, *stmt}
		}
	} else {
		for i := 0; i < len(stmt.body); i++ {
			curStmt, err := stmt.body[i].factStmt(nameDepths, true)
			if err != nil {
				return nil, nil, &parseTimeErr{err, *stmt}
			}
			section2Facts = append(section2Facts, curStmt)
		}
	}

	return section1Facts, section2Facts, nil
}

func (stmt *tokenBlock) defConFnStmt() (*ast.DefConFnStmt, error) {
	err := stmt.header.skip(glob.KeywordFn)
	if err != nil {
		return nil, &parseTimeErr{err, *stmt}
	}

	decl, nameDepths, err := stmt.conDefHeader()
	if err != nil {
		return nil, &parseTimeErr{err, *stmt}
	}

	retType, err := stmt.header.rawFc()
	if err != nil {
		return nil, &parseTimeErr{err, *stmt}
	}

	domFacts := []ast.FactStmt{}
	thenFacts := []*ast.SpecFactStmt{}

	if stmt.header.is(glob.KeySymbolColon) {
		stmt.header.skip()
		domFacts, thenFacts, err = stmt.bodyFactSectionSpecFactSection(glob.KeywordThen, nameDepths)
		if err != nil {
			return nil, &parseTimeErr{err, *stmt}
		}
	}

	return ast.NewDefConFnStmt(*decl, retType, domFacts, thenFacts), nil
}

func (stmt *tokenBlock) defObjStmt() (*ast.DefObjStmt, error) {
	err := stmt.header.skip(glob.KeywordObj)
	if err != nil {
		return nil, &parseTimeErr{err, *stmt}
	}

	objNames := []string{}
	objSets := []ast.Fc{}

	for !stmt.header.is(glob.KeySymbolColon) && !stmt.header.ExceedEnd() {
		decl, err := stmt.header.next()
		if err != nil {
			return nil, &parseTimeErr{err, *stmt}
		}
		if stmt.header.is(glob.KeySymbolComma) {
			err = stmt.header.skip(glob.KeySymbolColon)
			if err != nil {
				return nil, &parseTimeErr{err, *stmt}
			}
		}
		objNames = append(objNames, decl)
		tp, err := stmt.header.rawFc()
		if err != nil {
			return nil, &parseTimeErr{err, *stmt}
		}
		objSets = append(objSets, tp)
	}

	facts := []ast.FactStmt{}

	if !stmt.header.ExceedEnd() && stmt.header.is(glob.KeySymbolColon) {
		stmt.header.skip()
		facts, err = stmt.bodyFacts(nameDepthMap{})
		if err != nil {
			return nil, &parseTimeErr{err, *stmt}
		}
	} else if !stmt.header.ExceedEnd() {
		return nil, fmt.Errorf("expect ':' or end of block")
	}

	return ast.NewDefObjStmt(objNames, objSets, facts), nil
}

func (stmt *tokenBlock) claimStmt() (ast.ClaimStmt, error) {
	stmt.header.skip()
	err := error(nil)

	if err := stmt.header.testAndSkip(glob.KeySymbolColon); err != nil {
		return nil, &parseTimeErr{err, *stmt}
	}

	toCheck := &[]ast.FactStmt{}
	proof := &[]ast.Stmt{}

	for i := 0; i < len(stmt.body)-1; i++ {
		if !stmt.header.is(glob.KeywordProve) && !stmt.header.is(glob.KeywordProveByContradiction) {
			fact, err := stmt.body[i].factStmt(nameDepthMap{}, true)
			if err != nil {
				return nil, &parseTimeErr{err, *stmt}
			}
			*toCheck = append(*toCheck, fact)
		}
	}

	isProve := true
	if stmt.body[len(stmt.body)-1].header.is(glob.KeywordProveByContradiction) {
		isProve = false
	} else if !stmt.body[len(stmt.body)-1].header.is(glob.KeywordProve) {
		return nil, fmt.Errorf("expect 'prove' or 'prove_by_contradiction'")
	}
	stmt.body[len(stmt.body)-1].header.skip()

	err = stmt.body[len(stmt.body)-1].header.testAndSkip(glob.KeySymbolColon)
	if err != nil {
		return nil, &parseTimeErr{err, *stmt}
	}

	for _, block := range stmt.body[len(stmt.body)-1].body {
		curStmt, err := block.Stmt()
		if err != nil {
			return nil, &parseTimeErr{err, *stmt}
		}
		*proof = append(*proof, curStmt)
	}

	if isProve {
		return ast.NewClaimProveStmt(*toCheck, *proof), nil
	} else {
		return ast.NewClaimProveByContradictStmt(*toCheck, *proof), nil
	}
}

func (stmt *tokenBlock) proveClaimStmt() (*ast.ClaimProveStmt, error) {
	innerStmtArr, err := stmt.proveBlock()
	if err != nil {
		return nil, &parseTimeErr{err, *stmt}
	}
	return ast.NewClaimProveStmt([]ast.FactStmt{}, innerStmtArr), nil
}

func (stmt *tokenBlock) proveBlock() ([]ast.Stmt, error) {
	stmt.header.skip(glob.KeywordProve)
	if err := stmt.header.testAndSkip(glob.KeySymbolColon); err != nil {
		return nil, &parseTimeErr{err, *stmt}
	}

	innerStmtArr := []ast.Stmt{}
	for _, innerStmt := range stmt.body {
		curStmt, err := innerStmt.Stmt()
		if err != nil {
			return nil, &parseTimeErr{err, *stmt}
		}
		innerStmtArr = append(innerStmtArr, curStmt)
	}
	return innerStmtArr, nil
}

func (stmt *tokenBlock) knowStmt() (*ast.KnowStmt, error) {
	stmt.header.skip(glob.KeywordKnow)

	if !stmt.header.is(glob.KeySymbolColon) {
		facts := []ast.FactStmt{}
		fact, err := stmt.factStmt(nameDepthMap{}, true)
		if err != nil {
			return nil, &parseTimeErr{err, *stmt}
		}
		facts = append(facts, fact) // 之所以不能用,让know后面同一行里能有很多很多事实，是因为forall-fact是会换行的
		return ast.NewKnowStmt(facts), nil
	}

	if err := stmt.header.testAndSkip(glob.KeySymbolColon); err != nil {
		return nil, &parseTimeErr{err, *stmt}
	}

	facts, err := stmt.bodyFacts(nameDepthMap{})
	if err != nil {
		return nil, &parseTimeErr{err, *stmt}
	}

	return ast.NewKnowStmt(facts), nil
}

func (stmt *tokenBlock) defConExistPropStmt() (*ast.DefConExistPropStmt, error) {
	err := stmt.header.skip(glob.KeywordExistProp)
	if err != nil {
		return nil, &parseTimeErr{err, *stmt}
	}

	decl, nameDepths, err := stmt.conDefHeader()
	if err != nil {
		return nil, &parseTimeErr{err, *stmt}
	}

	existObjOrFn := []string{}
	existObjOrFnTypes := []*ast.FcAtom{}

	for !stmt.header.is(glob.KeySymbolColon) && !stmt.header.ExceedEnd() {
		decl, err := stmt.header.next()
		if err != nil {
			return nil, &parseTimeErr{err, *stmt}
		}
		tp, err := stmt.header.rawFcAtom()
		if err != nil {
			return nil, &parseTimeErr{err, *stmt}
		}
		existObjOrFn = append(existObjOrFn, decl)
		existObjOrFnTypes = append(existObjOrFnTypes, &tp)
		if stmt.header.is(glob.KeySymbolComma) {
			stmt.header.skip()
		}
	}

	err = stmt.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, &parseTimeErr{err, *stmt}
	}

	domFacts, thenFacts, err := stmt.bodyTwoFactSections(glob.KeywordIff, nameDepths)
	if err != nil {
		return nil, &parseTimeErr{err, *stmt}
	}

	return ast.NewDefConExistPropStmt(*decl, existObjOrFn, existObjOrFnTypes, domFacts, thenFacts), nil
}

func (stmt *tokenBlock) haveStmt() (*ast.HaveStmt, error) {
	stmt.header.skip(glob.KeywordHave)
	propStmt, err := stmt.specFactStmt(nameDepthMap{})
	if err != nil {
		return nil, &parseTimeErr{err, *stmt}
	}

	if !stmt.header.is(glob.KeySymbolColon) {
		return nil, fmt.Errorf("expected ':'")
	}

	if len(stmt.body) != 1 {
		return nil, fmt.Errorf("expect one string in members")
	}

	members, err := stmt.body[0].header.stringSliceUntilEnd()
	if err != nil {
		return nil, &parseTimeErr{err, *stmt}
	}

	return ast.NewHaveStmt(*propStmt, members), nil
}

// relaFact 只支持2个参数的关系
func (stmt *tokenBlock) relaFactStmt(nameDepths nameDepthMap) (*ast.SpecFactStmt, error) {
	fc, err := stmt.header.rawFc()
	if err != nil {
		return nil, &parseTimeErr{err, *stmt}
	}
	fc, err = ast.AddUniPrefixToFc(fc, nameDepths)
	if err != nil {
		return nil, &parseTimeErr{err, *stmt}
	}

	if stmt.header.strAtCurIndexPlus(0) == glob.KeywordIs {
		return stmt.header.isExpr(fc)
	}

	opt, err := stmt.header.next()
	if err != nil {
		return nil, &parseTimeErr{err, *stmt}
	}

	// 我认为没必要一定是内置的符号，可以是用户自定义的
	// if !glob.IsKeySymbolRelaProp(opt) {
	// 	return nil, &parseTimeErr{err, *stmt}
	// }

	fc2, err := stmt.header.rawFc()
	if err != nil {
		return nil, &parseTimeErr{err, *stmt}
	}
	fc2, err = ast.AddUniPrefixToFc(fc2, nameDepths)
	if err != nil {
		return nil, &parseTimeErr{err, *stmt}
	}

	params := []ast.Fc{fc, fc2}

	return ast.NewSpecFactStmt(true, ast.FcAtom{Value: opt}, params), nil
}

func (stmt *tokenBlock) axiomStmt() (*ast.AxiomStmt, error) {
	stmt.header.skip(glob.KeywordAxiom)
	decl, err := stmt.defPropExistStmt()
	if err != nil {
		return nil, &parseTimeErr{err, *stmt}
	}

	return ast.NewAxiomStmt(decl), nil
}

func (stmt *tokenBlock) thmStmt() (*ast.ThmStmt, error) {
	err := stmt.header.skip(glob.KeywordThm)
	if err != nil {
		return nil, &parseTimeErr{err, *stmt}
	}
	err = stmt.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, &parseTimeErr{err, *stmt}
	}
	if !stmt.header.ExceedEnd() {
		return nil, fmt.Errorf("expect end of line")
	}

	if len(stmt.body) != 2 {
		return nil, fmt.Errorf("expect two statements in thm")
	}

	decl, err := stmt.body[0].defPropExistStmt()
	if err != nil {
		return nil, &parseTimeErr{err, *stmt}
	}

	facts, err := stmt.body[1].proveBlock()
	if err != nil {
		return nil, &parseTimeErr{err, *stmt}
	}

	return ast.NewThmStmt(decl, facts), nil
}

func (stmt *tokenBlock) condFactStmt(nameDepths nameDepthMap) (*ast.CondFactStmt, error) {
	err := stmt.header.skip(glob.KeywordWhen)
	if err != nil {
		return nil, &parseTimeErr{err, *stmt}
	}
	err = stmt.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, &parseTimeErr{err, *stmt}
	}
	if !stmt.header.ExceedEnd() {
		return nil, fmt.Errorf("expect end of line")
	}

	condFacts := []ast.FactStmt{}
	thenFacts := []*ast.SpecFactStmt{}

	for i := 0; i < len(stmt.body)-1; i++ {
		fact, err := stmt.body[i].factStmt(nameDepths, true)
		if err != nil {
			return nil, &parseTimeErr{err, *stmt}
		}
		condFacts = append(condFacts, fact)
	}

	err = stmt.body[len(stmt.body)-1].header.skip(glob.KeywordThen)
	if err != nil {
		return nil, &parseTimeErr{err, *stmt}
	}
	err = stmt.body[len(stmt.body)-1].header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, &parseTimeErr{err, *stmt}
	}

	for i := len(stmt.body[len(stmt.body)-1].body) - 1; i >= 0; i-- {
		fact, err := stmt.body[len(stmt.body)-1].body[i].specFactStmt(nameDepths)
		if err != nil {
			return nil, &parseTimeErr{err, *stmt}
		}
		thenFacts = append(thenFacts, fact)
	}

	return ast.NewCondFactStmt(condFacts, thenFacts), nil
}

func (stmt *tokenBlock) defInterfaceStmt() (*ast.DefInterfaceStmt, error) {
	panic("")
}

func (stmt *tokenBlock) defTypeStmt() (*ast.DefTypeStmt, error) {
	panic("")
}

func (stmt *tokenBlock) conDefHeader() (*ast.ConDefHeader, nameDepthMap, error) {
	name, err := stmt.header.next()
	if err != nil {
		return nil, nil, &parseTimeErr{err, *stmt}
	}

	err = stmt.header.skip(glob.KeySymbolLeftBrace)
	if err != nil {
		return nil, nil, &parseTimeErr{err, *stmt}
	}

	params := []string{}
	typeParams := []ast.Fc{}
	nameDepths := nameDepthMap{}

	for !stmt.header.is(glob.KeySymbolRightBrace) {
		param, err := stmt.header.next()
		if err != nil {
			return nil, nil, &parseTimeErr{err, *stmt}
		}

		_, declared := nameDepths[param]
		if declared {
			return nil, nil, fmt.Errorf("duplicate parameter %s", param)
		}
		nameDepths[param] = 1

		typeParam, err := stmt.header.rawFc()
		if err != nil {
			return nil, nil, &parseTimeErr{err, *stmt}
		}

		typeParams = append(typeParams, typeParam)
		param = fmt.Sprintf("%s%s", glob.UniParamPrefix, param)
		params = append(params, param)

		if stmt.header.is(glob.KeySymbolComma) {
			stmt.header.skip()
		}
	}

	err = stmt.header.skip(glob.KeySymbolRightBrace)
	if err != nil {
		return nil, nil, &parseTimeErr{err, *stmt}
	}

	return ast.NewConDefHeader(name, params, typeParams), nameDepths, nil
}

func (stmt *tokenBlock) bodyFactSectionSpecFactSection(kw string, nameDepths nameDepthMap) ([]ast.FactStmt, []*ast.SpecFactStmt, error) {
	section1Facts := []ast.FactStmt{}
	section2SpecFacts := []*ast.SpecFactStmt{}
	err := error(nil)

	if stmt.body[len(stmt.body)-1].header.is(kw) {
		for i := 0; i < len(stmt.body)-1; i++ {
			curStmt, err := stmt.body[i].factStmt(nameDepths, true)
			if err != nil {
				return nil, nil, &parseTimeErr{err, *stmt}
			}
			section1Facts = append(section1Facts, curStmt)
		}
		section2SpecFacts, err = stmt.body[len(stmt.body)-1].thenBlockSpecFacts(nameDepths)
		if err != nil {
			return nil, nil, &parseTimeErr{err, *stmt}
		}
	} else {
		for i := 0; i < len(stmt.body); i++ {
			curStmt, err := stmt.body[i].specFactStmt(nameDepths)
			if err != nil {
				return nil, nil, &parseTimeErr{err, *stmt}
			}
			section2SpecFacts = append(section2SpecFacts, curStmt)
		}
	}

	return section1Facts, section2SpecFacts, nil
}

// * 我这里可以以这样的逻辑去实现这个函数，本质原因是specFact被当做rawFc去parse是不会报错的
func (b *tokenBlock) isSpecFactNotRelaFact() (bool, error) {
	curIndex := b.header.index
	defer b.setHeaderIndex(curIndex)

	_, err := b.header.rawFc()
	if err != nil {
		return false, err
	}

	if b.header.ExceedEnd() {
		return true, nil
	}
	return false, nil
}
