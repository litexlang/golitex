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

	slice, err := GetTopLevelStmtSlice(code)
	if err != nil {
		return nil, err
	}

	blocks := []TokenBlock{}
	for _, strBlock := range slice.Body {
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
	case Keywords["set_struct"]:
		ret, err = stmt.parseDefSetStructStmt()
	case Keywords["type"]:
		ret, err = stmt.parseDefTypeStmt()
	case Keywords["prop"]:
		ret, err = stmt.parseDefPropStmt()
	case Keywords["fn"]:
		ret, err = stmt.parseDefFnStmt()
	case Keywords["var"]:
		ret, err = stmt.parseDefVarStmt()
	case Keywords["claim"]:
		ret, err = stmt.parseClaimStmt()
	case Keywords["prove"]:
		ret, err = stmt.parseProveClaimStmt()
	case Keywords["know"]:
		ret, err = stmt.parseKnowStmt()
	case Keywords["exist"]:
		ret, err = stmt.parseDefExistStmt()
	case Keywords["have"]:
		ret, err = stmt.parseHaveStmt()
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

func (stmt *TokenBlock) parseTypeConceptDeclStmtKnows() (*[]FactStmt, error) {
	stmt.Header.next()
	if err := stmt.Header.testAndSkip(BuiltinSyms[":"]); err != nil {
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

func (block *TokenBlock) parseDefSetStructStmt() (*DefSetStructStmt, error) {
	block.Header.skip(Keywords["set_struct"])

	decl, err := block.Header.next()
	if err != nil {
		return nil, &parseStmtErr{err, *block}
	}

	structNameStr := ""
	if block.Header.is(Keywords["impl"]) {
		block.Header.next()
		structNameStr, err = block.Header.next()
		if err != nil {
			return nil, &parseStmtErr{err, *block}
		}
	}
	structName := TypeConceptStr(structNameStr)

	if !block.Header.is(BuiltinSyms[":"]) {
		return &DefSetStructStmt{decl, structName, []TypeMember{}, []InstanceMember{}, []FactStmt{}}, nil
	} else {
		block.Header.next()
	}

	typeMembers := []TypeMember{}
	instanceMembers := []InstanceMember{}
	knowFacts := &[]FactStmt{}

	for _, curStmt := range block.Body {
		if curStmt.Header.is(Keywords["type_member"]) {
			for _, member := range curStmt.Body {
				typeMember, err := member.parseTypeMember()
				if err != nil {
					return nil, &parseStmtErr{err, *block}
				}
				typeMembers = append(typeMembers, typeMember)
			}
		} else if curStmt.Header.is(Keywords["instance_member"]) {
			for _, member := range curStmt.Body {
				instanceMember, err := member.parseInstanceMember()
				if err != nil {
					return nil, &parseStmtErr{err, *block}
				}
				instanceMembers = append(instanceMembers, instanceMember)
			}
		} else if curStmt.Header.is(Keywords["know"]) {
			knowFacts, err = curStmt.parseTypeConceptDeclStmtKnows()
			if err != nil {
				return nil, &parseStmtErr{err, *block}
			}
		}
	}

	return &DefSetStructStmt{decl, structName, typeMembers, instanceMembers, *knowFacts}, nil

}

func (block *TokenBlock) parseDefTypeStmt() (*DefTypeStmt, error) {
	err := block.Header.skip(Keywords["type"])
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

	if !block.Header.is(BuiltinSyms[":"]) {
		return &DefTypeStmt{decl, []TypeMember{}, []InstanceMember{}, []FactStmt{}}, nil
	} else {
		block.Header.next()
	}

	typeMembers := []TypeMember{}
	instanceMembers := []InstanceMember{}
	knowFacts := &[]FactStmt{}

	for _, curStmt := range block.Body {
		if curStmt.Header.is(Keywords["type_member"]) {
			for _, member := range curStmt.Body {
				typeMember, err := member.parseTypeMember()
				if err != nil {
					return nil, &parseStmtErr{err, *block}
				}
				typeMembers = append(typeMembers, typeMember)
			}

		} else if curStmt.Header.is(Keywords["instance_member"]) {
			for _, member := range curStmt.Body {
				instanceMember, err := member.parseInstanceMember()
				if err != nil {
					return nil, &parseStmtErr{err, *block}
				}
				instanceMembers = append(instanceMembers, instanceMember)
			}

		} else if curStmt.Header.is(Keywords["know"]) {
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
	if stmt.Header.is(Keywords["forall"]) {
		return stmt.parseForallStmt()
	} else if stmt.Header.is(Keywords["when"]) {
		return stmt.parseIfStmt()
	}

	return stmt.parseInlineFactStmt()
}

func (stmt *TokenBlock) parseIfStmt() (FactStmt, error) {
	if stmt.Header.strAtIndex(-1) == BuiltinSyms[":"] {
		return stmt.parseBlockIfStmt()
	} else {
		return stmt.parseInlineIfFactStmt()
	}
}

func (stmt *TokenBlock) parseInlineFactStmt() (FactStmt, error) {
	if stmt.Header.is(Keywords["when"]) {
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

	varParams := &[]string{}
	condFacts := []FactStmt{}
	thenFacts := []SpecFactStmt{}

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

	return &BlockForallStmt{*varParams, condFacts, thenFacts}, nil
}

func (stmt *TokenBlock) parseInstantiatedFactStmt() (SpecFactStmt, error) {
	isTrue := true
	if stmt.Header.is(BuiltinSyms["not"]) {
		err := stmt.Header.skip(BuiltinSyms["not"])
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		isTrue = false
	}

	var ret SpecFactStmt
	var err error = nil
	if stmt.Header.is(BuiltinSyms["$"]) {
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
	err := stmt.Header.skip(BuiltinSyms["$"])
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	fc, err := stmt.Header.ParseFc()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	// * 为了防止 $p[a,b) 这样不小心把左括号输入错误了，然后fc取成p了，让)作为终止符
	if stmt.Header.strAtCurIndexPlus(-1) == BuiltinSyms[")"] {
		return &FuncFactStmt{true, fc}, nil
	} else {
		return nil, fmt.Errorf("expected ')', get %v", stmt.Header.strAtCurIndexPlus(-1))
	}
}

func (stmt *TokenBlock) parseBlockedForall() (FactStmt, error) {
	err := stmt.Header.skip(Keywords["forall"])
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	varParams, err := stmt.Header.parseFcVarTypePairArrEndWithColon()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	ifFacts := &[]FactStmt{}
	thenFacts := &[]SpecFactStmt{}

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
	if stmt.Header.strAtIndex(-1) != BuiltinSyms[":"] {
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

func (stmt *TokenBlock) parseInstantiatedFactsBlock() (*[]SpecFactStmt, error) {
	facts := &[]SpecFactStmt{}
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

func (stmt *TokenBlock) parseDefPropStmt() (*DefPropStmt, error) {
	decl, err := stmt.Header.parsePropDecl()
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

	return &DefFnStmt{decl.name, decl.vars, *ifFacts, *thenFacts}, nil
}

func (stmt *TokenBlock) parseDefVarStmt() (*DefVarStmt, error) {
	err := stmt.Header.skip(Keywords["var"])
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	varNames := []string{}

	for !stmt.Header.is(BuiltinSyms[":"]) && !stmt.Header.ExceedEnd() {
		decl, err := stmt.Header.next()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		if stmt.Header.is(BuiltinSyms[","]) {
			err = stmt.Header.skip(Keywords[","])
			if err != nil {
				return nil, &parseStmtErr{err, *stmt}
			}
		}
		varNames = append(varNames, decl)
	}

	ifFacts := &[]FactStmt{}

	if !stmt.Header.ExceedEnd() && stmt.Header.is(BuiltinSyms[":"]) {
		stmt.Header.skip()
		ifFacts, err = stmt.parseBodyFacts()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
	} else if !stmt.Header.ExceedEnd() {
		return nil, fmt.Errorf("expect ':' or end of block")
	}

	return &DefVarStmt{varNames, *ifFacts}, nil
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
	members := &[]InstanceMember{}
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
// 		// return stmt.Header.parseVarDecl()
// 		panic("unexpected var declaration")
// 	} else if stmt.Header.is(Keywords["prop"]) {
// 		return stmt.Header.parsePropDecl()
// 	}

// 	return nil, fmt.Errorf("expect 'fn', 'var', or 'prop'")
// }

func (stmt *TokenBlock) parseHaveStmt() (*HaveStmt, error) {
	stmt.Header.skip(Keywords["have"])
	propStmt, err := stmt.parseFuncPropFactStmt()
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

	return &HaveStmt{propStmt, *members}, nil
}

func (stmt *TokenBlock) parseRelationalFactStmt() (SpecFactStmt, error) {
	fc, err := stmt.Header.ParseFc()
	if err != nil {
		return nil, &parseStmtErr{err, *stmt}
	}

	if stmt.Header.strAtCurIndexPlus(0) == Keywords["is"] {
		return stmt.Header.parseIsExpr(fc)
	}

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

func (stmt *TokenBlock) parseInlineIfFactStmt() (*WhenCondFactStmt, error) {
	err := stmt.Header.skip(Keywords["when"])
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

	thenFacts := []SpecFactStmt{}

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

	return &WhenCondFactStmt{condFacts, thenFacts}, nil
}

func (stmt *TokenBlock) parseBlockIfStmt() (*WhenCondFactStmt, error) {
	err := stmt.Header.skip(Keywords["when"])
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
	thenFacts := []SpecFactStmt{}

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

	return &WhenCondFactStmt{condFacts, thenFacts}, nil
}
