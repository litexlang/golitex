package litexparser

import (
	"fmt"
	"strings"
)

type parseStmtErr struct {
	previous error
	stmt     TokenBlock
}

func (e *parseStmtErr) Error() string {
	curTok, err := e.stmt.Header.currentToken()
	if err != nil {
		return fmt.Sprintf("error at %s, column %d: %s", e.stmt.Header.String(), e.stmt.Header.getIndex(), e.previous.Error())
	} else {
		return fmt.Sprintf("error at %s, column %d, at '%s': %s", e.stmt.Header.String(), e.stmt.Header.getIndex(), curTok, e.previous.Error())
	}
}

func ParseSourceCode(code string) (*[]TopStmt, error) {
	code = strings.ReplaceAll(code, "\t", "    ")

	slice, err := getTopLevelStmtSlice(code)
	if err != nil {
		return nil, err
	}

	blocks := []TokenBlock{}
	for _, strBlock := range slice.body {
		block, err := TokenizeStmtBlock(&strBlock)
		if err != nil {
			return nil, err
		}
		blocks = append(blocks, *block)
	}

	ret := []TopStmt{}
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

func (stmt *TokenBlock) ParseTopLevelStmt() (*TopStmt, error) {
	pub := false
	if stmt.Header.is(BuiltinSyms["pub"]) {
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
	case Keywords["concept"]:
		ret, err = stmt.parseDefConceptStmt()
	case Keywords["type"]:
		ret, err = stmt.parseDefTypeStmt()
	case Keywords["prop"]:
		ret, err = stmt.parseDefPropertyStmt()
	case Keywords["fn"]:
		ret, err = stmt.parseDefFnStmt()
	case Keywords["var"]:
		ret, err = stmt.parseDefVarStmt()
	case Keywords["claim"]:
		ret, err = stmt.parseClaimStmt()
	case Keywords["prove"]:
		ret, err = stmt.parseProveClaimStmt()
	case Keywords["alias"]:
		ret, err = stmt.parseDefAliasStmt()
	case Keywords["know"]:
		ret, err = stmt.parseKnowStmt()
	case Keywords["exist"]:
		ret, err = stmt.parseDefExistStmt()
	case Keywords["have"]:
		ret, err = stmt.parseHaveStmt()
	case Keywords["member"]:
		ret, err = stmt.parseMemberStmt()
	case Keywords["type_member"]:
		ret, err = stmt.parseTypeMemberStmt()
	case Keywords["axiom"]:
		ret, err = stmt.parseAxiomStmt()
	case Keywords["thm"]:
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

func (p *TokenBlock) parseFcMember() (*[]FcVarDecl, *[]FcFnDecl, *[]PropDecl, error) {
	p.Header.next()
	if err := p.Header.testAndSkip(BuiltinSyms[":"]); err != nil {
		return nil, nil, nil, err
	}

	varMember := &[]FcVarDecl{}
	fnMember := &[]FcFnDecl{}
	propertyMember := &[]PropDecl{}

	for _, curStmt := range p.Body {
		if curStmt.Header.is(Keywords["var"]) {
			member, err := curStmt.Header.parseVarDecl()
			if err != nil {
				return nil, nil, nil, err
			}
			*varMember = append(*varMember, *member)
		} else if curStmt.Header.is(Keywords["fn"]) {
			member, err := curStmt.Header.parseFcFnDecl()
			if err != nil {
				return nil, nil, nil, err
			}
			*fnMember = append(*fnMember, *member)
		} else if curStmt.Header.is(Keywords["prop"]) {
			member, err := curStmt.Header.parsePropertyDecl()
			if err != nil {
				return nil, nil, nil, err
			}
			*propertyMember = append(*propertyMember, *member)
		}
	}

	return varMember, fnMember, propertyMember, nil
}

func (stmt *TokenBlock) parseThenFacts() (*[]FactStmt, error) {
	stmt.Header.next()
	if err := stmt.Header.testAndSkip(BuiltinSyms[":"]); err != nil {
		return nil, err
	}

	facts := &[]FactStmt{}

	for _, curStmt := range stmt.Body {
		if curStmt.Header.is(Keywords["fact"]) {
			fact, err := curStmt.parseFactStmt()
			if err != nil {
				return nil, err
			}
			*facts = append(*facts, fact)
		}
	}

	return facts, nil
}

// func (p *tokenBlock) parseFnRetTypeMember() (*[]fnRetTypeMemberDecl, error) {
// 	p.header.next()
// 	if err := p.header.testAndSkip(BuiltinSyms[":"]); err != nil {
// 		return nil, err
// 	}

// 	member := &[]fnRetTypeMemberDecl{}

// 	for _, curStmt := range p.body {
// 		if curStmt.header.is(Keywords["var"]) {
// 			v, err := curStmt.header.parseVarDecl()
// 			if err != nil {
// 				return nil, err
// 			}
// 			*member = append(*member, v)
// 		} else if curStmt.header.is(Keywords["fn"]) {
// 			v, err := curStmt.header.parseFcFnDecl()
// 			if err != nil {
// 				return nil, err
// 			}
// 			*member = append(*member, v)

// 		} else {
// 			return nil, fmt.Errorf("unexpected declaration %v", curStmt.header)
// 		}
// 	}

// 	return member, nil
// }

func (stmt *TokenBlock) parseDefConceptStmt() (*DefConceptStmt, error) {
	stmt.Header.skip(Keywords["concept"])

	decl, err := stmt.parseFcDecl()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	conceptNameStr := ""
	if stmt.Header.is(Keywords["impl"]) {
		stmt.Header.next()
		conceptNameStr, err = stmt.Header.next()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
	}
	conceptName := TypeConceptStr(conceptNameStr)

	if !stmt.Header.is(BuiltinSyms[":"]) {
		return &DefConceptStmt{decl, (conceptName), []FcVarDecl{}, []FcFnDecl{}, []PropDecl{}, []FcVarDecl{}, []FcFnDecl{}, []PropDecl{}, []FactStmt{}}, nil
	} else {
		stmt.Header.next()
	}

	typeVarMember := &[]FcVarDecl{}
	typeFnMember := &[]FcFnDecl{}
	typePropertyMember := &[]PropDecl{}
	varMember := &[]FcVarDecl{}
	fnMember := &[]FcFnDecl{}
	propertyMember := &[]PropDecl{}
	thenFacts := &[]FactStmt{}

	for _, curStmt := range stmt.Body {
		if curStmt.Header.is(Keywords["type_member"]) {
			typeVarMember, typeFnMember, typePropertyMember, err = curStmt.parseFcMember()
			if err != nil {
				return nil, &parseStmtErr{err, *stmt}
			}
		} else if curStmt.Header.is(Keywords["member"]) {
			varMember, fnMember, propertyMember, err = curStmt.parseFcMember()
			if err != nil {
				return nil, &parseStmtErr{err, *stmt}
			}
		} else if curStmt.Header.is(Keywords["then"]) {
			thenFacts, err = curStmt.parseThenFacts()
			if err != nil {
				return nil, &parseStmtErr{err, *stmt}
			}
		}
	}

	return &DefConceptStmt{decl, (conceptName), *typeVarMember, *typeFnMember, *typePropertyMember, *varMember, *fnMember, *propertyMember, *thenFacts}, nil

}

func (stmt *TokenBlock) parseDefTypeStmt() (*DefTypeStmt, error) {
	err := stmt.Header.skip(Keywords["type"])
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	implName := &NamedFcType{}

	if stmt.Header.is(Keywords["impl"]) {
		stmt.Header.next()
		implName, err = stmt.Header.parseNamedFcType()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
	}

	if !stmt.Header.is(Keywords["fn"]) && !stmt.Header.is(Keywords["prop"]) && !stmt.Header.is(Keywords["var"]) {
		typeName, err := stmt.Header.next()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}

		decl := FcVarDecl{FcVarDeclPair{"", FcVarType{"", FcVarTypeStrValue(typeName)}}}

		return &DefTypeStmt{&decl, *implName, []FcVarDecl{}, []FcFnDecl{}, []PropDecl{}, []FcVarDecl{}, []FcFnDecl{}, []PropDecl{}, []FactStmt{}}, nil
	}

	decl, err := stmt.parseFcDecl()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	if !stmt.Header.is(BuiltinSyms[":"]) {
		return &DefTypeStmt{decl, *implName, []FcVarDecl{}, []FcFnDecl{}, []PropDecl{}, []FcVarDecl{}, []FcFnDecl{}, []PropDecl{}, []FactStmt{}}, nil
	} else {
		stmt.Header.next()
	}

	typeVarMember := &[]FcVarDecl{}
	typeFnMember := &[]FcFnDecl{}
	typePropertyMember := &[]PropDecl{}
	varMember := &[]FcVarDecl{}
	fnMember := &[]FcFnDecl{}
	propertyMember := &[]PropDecl{}
	thenFacts := &[]FactStmt{}

	for _, curStmt := range stmt.Body {
		if curStmt.Header.is(Keywords["type_member"]) {
			typeVarMember, typeFnMember, typePropertyMember, err = curStmt.parseFcMember()
			if err != nil {
				return nil, &parseStmtErr{err, *stmt}
			}
		} else if curStmt.Header.is(Keywords["member"]) {
			varMember, fnMember, propertyMember, err = curStmt.parseFcMember()
			if err != nil {
				return nil, &parseStmtErr{err, *stmt}
			}
		} else if curStmt.Header.is(Keywords["then"]) {
			thenFacts, err = curStmt.parseThenFacts()
			if err != nil {
				return nil, &parseStmtErr{err, *stmt}
			}
		}
	}
	return &DefTypeStmt{decl, *implName, *typeVarMember, *typeFnMember, *typePropertyMember, *varMember, *fnMember, *propertyMember, *thenFacts}, nil
}

func (stmt *TokenBlock) parseFactStmt() (FactStmt, error) {
	if stmt.Header.is(Keywords["forall"]) {
		return stmt.parseForallStmt()
	} else if stmt.Header.is(Keywords["if"]) {
		return stmt.parseIfStmt()
	}

	return stmt.parseInlineFactStmt()
}

func (stmt *TokenBlock) parseIfStmt() (FactStmt, error) {
	if stmt.Header.strAt(-1) == BuiltinSyms[":"] {
		return stmt.parseBlockIfStmt()
	} else {
		return stmt.parseInlineIfFactStmt()
	}
}

func (stmt *TokenBlock) parseInlineFactStmt() (FactStmt, error) {
	if stmt.Header.is(Keywords["if"]) {
		return stmt.parseInlineIfFactStmt()
	} else if stmt.Header.is(Keywords["forall"]) {
		return stmt.parseInlineForallStmt()
	}

	return stmt.parseInstantiatedFactStmt()
}

func (stmt *TokenBlock) parseInlineForallStmt() (*BlockForallStmt, error) {
	err := stmt.Header.skip(Keywords["forall"])
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	typeParams := &[]TypeConceptPair{}
	varParams := &[]StrTypePair{}
	condFacts := []FactStmt{}
	thenFacts := []InstantiatedFactStmt{}

	typeParams, varParams, err = stmt.Header.parseBracketedTypeConceptPairArrAndBracedFcTypePairArr()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	for !stmt.Header.is(BuiltinSyms["{"]) {
		fact, err := stmt.parseInlineFactStmt()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		condFacts = append(condFacts, fact)

		if stmt.Header.is(BuiltinSyms[","]) {
			stmt.Header.next()
		}
	}

	err = stmt.Header.skip(BuiltinSyms["{"])
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	for !stmt.Header.is(BuiltinSyms["}"]) {
		fact, err := stmt.parseInstantiatedFactStmt()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		thenFacts = append(thenFacts, fact)

		if stmt.Header.is(BuiltinSyms[","]) {
			stmt.Header.next()
		}
	}
	err = stmt.Header.skip(BuiltinSyms["}"])
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	return &BlockForallStmt{*typeParams, *varParams, condFacts, thenFacts}, nil
}

func (stmt *TokenBlock) parseInstantiatedFactStmt() (InstantiatedFactStmt, error) {
	isTrue := true
	if stmt.Header.is(BuiltinSyms["not"]) {
		err := stmt.Header.skip(BuiltinSyms["not"])
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		isTrue = false
	}

	var ret InstantiatedFactStmt
	var err error = nil
	if stmt.Header.is(BuiltinSyms["$"]) {
		ret, err = stmt.parseFuncPropertyFactStmt()
	} else {
		ret, err = stmt.parseRelationalFactStmt()
	}

	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	ret.notFactStmtSetT(isTrue)
	return ret, nil
}

func (stmt *TokenBlock) parseFuncPropertyFactStmt() (*FuncPropStmt, error) {
	err := stmt.Header.skip(BuiltinSyms["$"])
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	fc, err := stmt.Header.ParseFc()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	return &FuncPropStmt{true, fc}, nil
}

func (stmt *TokenBlock) parseBlockedForall() (FactStmt, error) {
	err := stmt.Header.skip(Keywords["forall"])
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	typeParams := &[]TypeConceptPair{}
	if stmt.Header.is(BuiltinSyms["["]) {
		typeParams, err = stmt.Header.parseBracketedTypeConceptPairArray()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
	}

	varParams, err := stmt.Header.parseFcVarTypePairArrEndWithColon()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	ifFacts := &[]FactStmt{}
	thenFacts := &[]InstantiatedFactStmt{}

	if len(stmt.Body) > 0 && (stmt.Body)[0].Header.is(Keywords["cond"]) {
		ifFacts, err = stmt.Body[0].parseForallCondFactsBlock()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}

		if len(stmt.Body) == 2 && (stmt.Body)[1].Header.is(Keywords["then"]) {
			thenFacts, err = stmt.Body[1].parseInstantiatedFactsBlock()
			if err != nil {
				return nil, &parseStmtErr{err, *stmt}
			}
		} else {
			return nil, fmt.Errorf("expected 'then'")
		}
	} else {
		thenFacts, err = stmt.parseInstantiatedFactsBlock()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
	}

	return &BlockForallStmt{*typeParams, *varParams, *ifFacts, *thenFacts}, nil
}

func (stmt *TokenBlock) parseForallStmt() (FactStmt, error) {
	if stmt.Header.strAt(-1) != BuiltinSyms[":"] {
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
	err := stmt.Header.parseGivenWordsThenExceedEnd(&[]string{Keywords["cond"], BuiltinSyms[":"]})
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	facts, err := stmt.parseBodyFacts()
	return facts, err
}

// func (stmt *TokenBlock) parseBodyInlineFacts() (*[]InlineFactStmt, error) {
// 	if len(stmt.Body) == 0 {
// 		return &[]InlineFactStmt{}, nil
// 	}

// 	facts := &[]InlineFactStmt{}
// 	for _, f := range stmt.Body {
// 		fact, err := f.parseInlineFactStmt()
// 		if err != nil {
// 			return nil, &parseStmtErr{err, *stmt}
// 		}
// 		*facts = append(*facts, fact)
// 	}

// 	return facts, nil
// }

// func (stmt *TokenBlock) parseInlineFactsBlock() (*[]InlineFactStmt, error) {
// 	facts := &[]InlineFactStmt{}
// 	stmt.Header.skip()
// 	if err := stmt.Header.testAndSkip(BuiltinSyms[":"]); err != nil {
// 		return nil, &parseStmtErr{err, *stmt}
// 	}

// 	for _, curStmt := range stmt.Body {
// 		fact, err := curStmt.parseInlineFactStmt()
// 		if err != nil {
// 			return nil, &parseStmtErr{err, *stmt}
// 		}
// 		*facts = append(*facts, fact)
// 	}

// 	return facts, nil
// }

func (stmt *TokenBlock) parseInstantiatedFactsBlock() (*[]InstantiatedFactStmt, error) {
	facts := &[]InstantiatedFactStmt{}
	stmt.Header.skip()
	if err := stmt.Header.testAndSkip(BuiltinSyms[":"]); err != nil {
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

func (stmt *TokenBlock) parseDefPropertyStmt() (*DefPropStmt, error) {
	decl, err := stmt.Header.parsePropertyDecl()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	ifFacts := &[]FactStmt{}
	thenFacts := &[]FactStmt{}
	if stmt.Header.is(BuiltinSyms[":"]) {
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

	if len(stmt.Body) == 2 && stmt.Body[0].Header.is(Keywords["cond"]) && stmt.Body[1].Header.is(Keywords["then"]) {
		stmt.Body[0].Header.skip()
		if err := stmt.Body[0].Header.testAndSkip(BuiltinSyms[":"]); err != nil {
			return nil, nil, err
		}

		ifFacts, err = stmt.Body[0].parseBodyFacts()
		if err != nil {
			return nil, nil, err
		}

		stmt.Body[1].Header.skip()
		if err := stmt.Body[1].Header.testAndSkip(BuiltinSyms[":"]); err != nil {
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

	if stmt.Header.is(BuiltinSyms[":"]) {
		stmt.Header.skip()
		ifFacts, thenFacts, err = stmt.parseBodyCondFactsThenFacts()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
	}

	return &DefFnStmt{decl.name, decl.tp, *ifFacts, *thenFacts}, nil
}

func (stmt *TokenBlock) parseDefVarStmt() (*DefVarStmt, error) {
	decl, err := stmt.Header.parseVarDecl()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	ifFacts := &[]FactStmt{}

	if stmt.Header.is(BuiltinSyms[":"]) {
		stmt.Header.skip()
		ifFacts, err = stmt.parseBodyFacts()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
	} else if !stmt.Header.ExceedEnd() {
		return nil, fmt.Errorf("expect ':' or end of block")
	}

	return &DefVarStmt{*decl, *ifFacts}, nil
}

func (stmt *TokenBlock) parseClaimStmt() (ClaimStmt, error) {
	stmt.Header.skip()
	var err error = nil

	if err := stmt.Header.testAndSkip(BuiltinSyms[":"]); err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	toCheck := &[]FactStmt{}
	proof := &[]Stmt{}

	for i := 0; i < len(stmt.Body)-1; i++ {
		if !stmt.Header.is(Keywords["prove"]) && !stmt.Header.is(Keywords["prove_by_contradiction"]) {
			fact, err := stmt.Body[i].parseFactStmt()
			if err != nil {
				return nil, &parseStmtErr{err, *stmt}
			}
			*toCheck = append(*toCheck, fact)
		}
	}

	isProve := true
	if stmt.Body[len(stmt.Body)-1].Header.is(Keywords["prove_by_contradiction"]) {
		isProve = false
	} else if !stmt.Body[len(stmt.Body)-1].Header.is(Keywords["prove"]) {
		return nil, fmt.Errorf("expect 'prove' or 'prove_by_contradiction'")
	}
	stmt.Body[len(stmt.Body)-1].Header.skip()

	err = stmt.Body[len(stmt.Body)-1].Header.testAndSkip(Keywords[":"])
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
	stmt.Header.skip(Keywords["prove"])
	if err := stmt.Header.testAndSkip(BuiltinSyms[":"]); err != nil {
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

func (stmt *TokenBlock) parseDefAliasStmt() (*DefAliasStmt, error) {
	stmt.Header.skip(Keywords["alias"])

	previous, err := stmt.Header.next()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	newName, err := stmt.Header.next()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	return &DefAliasStmt{previous, newName}, nil
}

func (stmt *TokenBlock) parseKnowStmt() (*KnowStmt, error) {
	stmt.Header.skip(Keywords["know"])

	if !stmt.Header.is(BuiltinSyms[":"]) {
		facts := []FactStmt{}
		fact, err := stmt.parseFactStmt()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		facts = append(facts, fact) // 之所以不能用,让know后面同一行里能有很多很多事实，是因为forall-fact是会换行的
		return &KnowStmt{facts}, nil
	}

	if err := stmt.Header.testAndSkip(BuiltinSyms[":"]); err != nil {
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
	member := &[]fcDecl{}
	thenFacts := &[]FactStmt{}
	if !stmt.Header.is(BuiltinSyms[":"]) {
		return nil, fmt.Errorf("expected ':‘")
	}

	stmt.Header.skip(BuiltinSyms[":"])

	for _, curStmt := range stmt.Body {
		if curStmt.Header.is(Keywords["cond"]) {
			ifFacts, err = curStmt.parseBodyFacts()
			if err != nil {
				return nil, &parseStmtErr{err, *stmt}
			}
			continue
		}
		if curStmt.Header.is(Keywords["then"]) {
			thenFacts, err = curStmt.parseBodyFacts()
			if err != nil {
				return nil, &parseStmtErr{err, *stmt}
			}
			continue
		}
		if curStmt.Header.is(Keywords["members"]) {
			member, err = curStmt.parseFcDecls()
			if err != nil {
				return nil, &parseStmtErr{err, *stmt}
			}
			continue
		}
	}

	return &DefExistStmt{*decl, *ifFacts, *member, *thenFacts}, nil
}

func (stmt *TokenBlock) parseFcDecls() (*[]fcDecl, error) {
	ret := []fcDecl{}

	for _, curStmt := range stmt.Body {
		cur, err := curStmt.parseFcDecl()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		ret = append(ret, cur)
	}

	return &ret, nil
}

func (stmt *TokenBlock) parseFcDecl() (fcDecl, error) {
	if stmt.Header.is(Keywords["fn"]) {
		return stmt.Header.parseFcFnDecl()
	} else if stmt.Header.is(Keywords["var"]) {
		return stmt.Header.parseVarDecl()
	} else if stmt.Header.is(Keywords["prop"]) {
		return stmt.Header.parsePropertyDecl()
	}

	return nil, fmt.Errorf("expect 'fn', 'var', or 'property'")
}

func (stmt *TokenBlock) parseHaveStmt() (*HaveStmt, error) {
	stmt.Header.skip(Keywords["have"])
	propertyStmt, err := stmt.parseFuncPropertyFactStmt()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	if !stmt.Header.is(BuiltinSyms[":"]) {
		return nil, fmt.Errorf("expected ':'")
	}

	if len(stmt.Body) != 1 {
		return nil, fmt.Errorf("expect one string in members")
	}

	members, err := stmt.Body[0].Header.parseStringArrUntilEnd()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	return &HaveStmt{propertyStmt, *members}, nil
}

func (stmt *TokenBlock) parseMemberStmt() (*DefMemberStmt, error) {
	stmt.Header.skip(Keywords["member"])

	typeConcepts, err := stmt.Header.parseBracketedTypeConceptPairArray()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	if len(*typeConcepts) != 1 {
		return nil, fmt.Errorf("expect one type concept in members")
	}

	typeConcept := (*typeConcepts)[0]

	varTypes, err := stmt.Header.parseBracedFcStrTypePairArray()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	if len(*varTypes) != 1 {
		return nil, fmt.Errorf("expect one type in members")
	}

	varType := (*varTypes)[0]

	var decl fcDecl

	if stmt.Header.is(Keywords["var"]) {
		decl, err = stmt.Header.parseVarDecl()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
	} else if stmt.Header.is(Keywords["fn"]) {
		decl, err = stmt.Header.parseFcFnDecl()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
	} else if stmt.Header.is(Keywords["prop"]) {
		decl, err = stmt.Header.parsePropertyDecl()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
	} else {
		return nil, fmt.Errorf("expect 'var', 'fn', or 'property'")
	}

	if stmt.Header.ExceedEnd() {
		return &DefMemberStmt{typeConcept, varType, decl, []FactStmt{}}, nil
	}

	if err := stmt.Header.testAndSkip(BuiltinSyms[":"]); err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	facts, err := stmt.parseBodyFacts()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	return &DefMemberStmt{typeConcept, varType, decl, *facts}, nil
}

func (stmt *TokenBlock) parseTypeMemberStmt() (*DefTypeMemberStmt, error) {
	stmt.Header.skip(Keywords["type_member"])

	typeConcepts, err := stmt.Header.parseBracketedTypeConceptPairArray()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	if len(*typeConcepts) != 1 {
		return nil, fmt.Errorf("expect one type concept in members")
	}

	typeConcept := (*typeConcepts)[0]

	var decl fcDecl

	if stmt.Header.is(Keywords["var"]) {
		decl, err = stmt.Header.parseVarDecl()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
	} else if stmt.Header.is(Keywords["fn"]) {
		decl, err = stmt.Header.parseFcFnDecl()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
	} else if stmt.Header.is(Keywords["prop"]) {
		decl, err = stmt.Header.parsePropertyDecl()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
	} else {
		return nil, fmt.Errorf("expect 'var', 'fn', or 'property'")
	}

	if stmt.Header.ExceedEnd() {
		return &DefTypeMemberStmt{typeConcept, decl, []FactStmt{}}, nil
	}

	if err := stmt.Header.testAndSkip(BuiltinSyms[":"]); err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	facts, err := stmt.parseBodyFacts()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	return &DefTypeMemberStmt{typeConcept, decl, *facts}, nil
}

func (stmt *TokenBlock) parseRelationalFactStmt() (InstantiatedFactStmt, error) {
	fc, err := stmt.Header.ParseFc()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	opt, err := stmt.Header.next()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	if opt == Keywords["is"] {
		return stmt.Header.parseIsExpr(fc)
	}

	if !isBuiltinRelationalOperator(opt) {
		return nil, &parseStmtErr{err, *stmt}
	}

	fc2, err := stmt.Header.ParseFc()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	vars := []Fc{fc, fc2}
	for stmt.Header.is(opt) {
		stmt.Header.skip()
		fc, err := stmt.Header.ParseFc()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		vars = append(vars, fc)
	}

	return &RelationFactStmt{true, vars, FcStr(opt)}, nil
}

func (stmt *TokenBlock) parseAxiomStmt() (*AxiomStmt, error) {
	stmt.Header.skip(Keywords["axiom"])
	decl, err := stmt.parseDefPropExistStmt()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	return &AxiomStmt{decl}, nil
}

func (stmt *TokenBlock) parseThmStmt() (*ThmStmt, error) {
	err := stmt.Header.skip(Keywords["thm"])
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}
	err = stmt.Header.skip(BuiltinSyms[":"])
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

func (stmt *TokenBlock) parseInlineIfFactStmt() (*IfFactStmt, error) {
	err := stmt.Header.skip(Keywords["if"])
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	condFacts := []FactStmt{}
	for !stmt.Header.is(BuiltinSyms["{"]) {
		fact, err := stmt.parseInlineFactStmt()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		condFacts = append(condFacts, fact)

		if stmt.Header.is(BuiltinSyms[","]) {
			stmt.Header.skip()
		}
	}

	thenFacts := []InstantiatedFactStmt{}

	err = stmt.Header.skip(BuiltinSyms["{"])
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	for !stmt.Header.is(BuiltinSyms["}"]) {
		fact, err := stmt.parseInstantiatedFactStmt()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		thenFacts = append(thenFacts, fact)

		if stmt.Header.is(BuiltinSyms[","]) {
			stmt.Header.skip()
		}
	}

	err = stmt.Header.skip(BuiltinSyms["}"])
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	return &IfFactStmt{condFacts, thenFacts}, nil
}

func (stmt *TokenBlock) parseBlockIfStmt() (*IfFactStmt, error) {
	err := stmt.Header.skip(Keywords["if"])
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}
	err = stmt.Header.skip(BuiltinSyms[":"])
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}
	if !stmt.Header.ExceedEnd() {
		return nil, fmt.Errorf("expect end of line")
	}

	condFacts := []FactStmt{}
	thenFacts := []InstantiatedFactStmt{}

	for i := 0; i < len(stmt.Body)-1; i++ {
		fact, err := stmt.Body[i].parseInstantiatedFactStmt()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		condFacts = append(condFacts, fact)
	}

	err = stmt.Body[len(stmt.Body)-1].Header.skip(Keywords["then"])
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}
	err = stmt.Body[len(stmt.Body)-1].Header.skip(BuiltinSyms[":"])
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

	return &IfFactStmt{condFacts, thenFacts}, nil
}
