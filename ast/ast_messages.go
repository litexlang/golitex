// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Litex email: <litexlang@outlook.com>
// Litex website: https://litexlang.com
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_ast

import (
	"fmt"
	glob "golitex/glob"
	"strings"
)

func (stmt *KnowFactStmt) String() string {
	var builder strings.Builder

	if len(stmt.Facts) == 0 {
		return ""
	}

	builder.WriteString(glob.KeywordKnow)

	if len(stmt.Facts) > 1 {
		builder.WriteString(glob.KeySymbolColon)
		builder.WriteByte('\n')

		factStrSlice := make([]string, len(stmt.Facts))
		for i := range len(stmt.Facts) {
			factStrSlice[i] = glob.SplitLinesAndAdd4NIndents(stmt.Facts[i].String(), 1)
		}
		builder.WriteString(strings.Join(factStrSlice, "\n"))
		return builder.String()
	} else {
		builder.WriteString(" ")
		builder.WriteString(stmt.Facts[0].String())
		return builder.String()
	}
}

func (stmt *SpecFactStmt) StringWithLine() string {
	if stmt.GetLine() == 0 {
		return fmt.Sprintf("%s\na builtin fact", stmt.String())
	} else {
		return fmt.Sprintf("%s on line %d", stmt.String(), stmt.GetLine())
	}
}

func (stmt *SpecFactStmt) String() string {
	if stmt.IsExist_St_Fact() {
		return exist_st_FactString(stmt)
	} else {
		return pureSpecFactString(stmt)
	}
}

var relaPropSet map[string]struct{} = map[string]struct{}{
	glob.KeywordIn: {},
}

func pureSpecFactString(stmt *SpecFactStmt) string {
	var builder strings.Builder

	if stmt.TypeEnum == FalsePure {
		builder.WriteString(glob.KeywordNot)
		builder.WriteByte(' ')
	}

	if glob.IsKeySymbol(string(stmt.PropName)) {
		builder.WriteString(keySymbolRelaFactWithoutNotString(stmt))
	} else if _, ok := relaPropSet[string(stmt.PropName)]; ok {
		builder.WriteString(keywordRelaFactWithoutNotString(stmt))
	} else {
		builder.WriteString(glob.FuncFactPrefix)
		builder.WriteString(stmt.PropName.String())
		builder.WriteByte('(')

		builder.WriteString(objSliceString(stmt.Params))
		builder.WriteByte(')')
	}
	return builder.String()
}

func keywordRelaFactWithoutNotString(stmt *SpecFactStmt) string {
	var builder strings.Builder

	builder.WriteString(stmt.Params[0].String())
	builder.WriteByte(' ')
	builder.WriteString(glob.KeySymbolDollar)
	builder.WriteString(stmt.PropName.String())
	builder.WriteByte(' ')
	builder.WriteString(stmt.Params[1].String())

	return builder.String()
}

func keySymbolRelaFactWithoutNotString(stmt *SpecFactStmt) string {
	var builder strings.Builder

	builder.WriteString(stmt.Params[0].String())
	builder.WriteByte(' ')
	builder.WriteString(stmt.PropName.String())
	builder.WriteByte(' ')
	builder.WriteString(stmt.Params[1].String())

	return builder.String()
}

func StrObjSetPairs(objs []string, objSets []Obj) string {
	pairStrSlice := make([]string, len(objs))
	for i := range len(objs) {
		pairStrSlice[i] = fmt.Sprintf("%s %s", objs[i], objSets[i])
	}
	return strings.Join(pairStrSlice, ", ")
}

func exist_st_FactString(stmt *SpecFactStmt) string {
	var builder strings.Builder
	if stmt.TypeEnum == FalseExist_St {
		builder.WriteString(glob.KeywordNot)
		builder.WriteByte(' ')
	}

	builder.WriteString(glob.KeywordExist)
	builder.WriteByte(' ')

	existParams, factParams := GetExistFactExistParamsAndFactParams(stmt)

	builder.WriteString(objSliceString(existParams))
	builder.WriteString(" ")
	builder.WriteString(glob.KeywordSt)
	builder.WriteString(" ")
	builder.WriteString(NewSpecFactStmt(TruePure, stmt.PropName, factParams, glob.BuiltinLine).String())

	return builder.String()
}

func (stmt *DefLetStmt) String() string {
	var builder strings.Builder

	builder.WriteString(glob.KeywordLet)
	builder.WriteString(" ")
	builder.WriteString(StrObjSetPairs(stmt.Objs, stmt.ObjSets))

	if len(stmt.Facts) > 0 {
		builder.WriteString(glob.KeySymbolColon)
		builder.WriteByte('\n')
		factStrSlice := make([]string, len(stmt.Facts))
		for i := range len(stmt.Facts) {
			factStrSlice[i] = glob.SplitLinesAndAdd4NIndents(stmt.Facts[i].String(), 1)
		}
		builder.WriteString(strings.Join(factStrSlice, "\n"))
	}

	return builder.String()
}

func (stmt *HaveObjInNonEmptySetStmt) String() string {
	var builder strings.Builder

	builder.WriteString(glob.KeywordHave)
	builder.WriteString(" ")
	builder.WriteString(StrObjSetPairs(stmt.Objs, stmt.ObjSets))

	return builder.String()
}

func (fact *DefPropStmt) String() string {
	var builder strings.Builder

	builder.WriteString(glob.KeywordProp)
	builder.WriteByte(' ')
	builder.WriteString(fact.DefHeader.String())

	if len(fact.DomFactsOrNil) == 0 && len(fact.IffFactsOrNil) == 0 {
		return strings.TrimSuffix(builder.String(), glob.KeySymbolColon)
	}

	builder.WriteByte('\n')
	if len(fact.DomFactsOrNil) > 0 {
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(glob.KeywordDom, 1))
		builder.WriteString(glob.KeySymbolColon)
		builder.WriteByte('\n')
		domFactStrSlice := make([]string, len(fact.DomFactsOrNil))
		for i := range len(fact.DomFactsOrNil) {
			domFactStrSlice[i] = glob.SplitLinesAndAdd4NIndents(fact.DomFactsOrNil[i].String(), 2)
		}
		builder.WriteString(strings.Join(domFactStrSlice, "\n"))
		builder.WriteByte('\n')
	}

	if len(fact.IffFactsOrNil) > 0 {
		// builder.WriteString(glob.SplitLinesAndAdd4NIndents(glob.KeywordIff, 1))
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(glob.KeySymbolEquivalent, 1))
		builder.WriteString(glob.KeySymbolColon)
		builder.WriteByte('\n')
		iffFactStrSlice := make([]string, len(fact.IffFactsOrNil))
		for i := range len(fact.IffFactsOrNil) {
			iffFactStrSlice[i] = glob.SplitLinesAndAdd4NIndents(fact.IffFactsOrNil[i].String(), 2)
		}
		builder.WriteString(strings.Join(iffFactStrSlice, "\n"))
	}

	return builder.String()

}

func fnDefStmtStringGivenKw(kw string, f *FnTStruct, name string) string {
	var builder strings.Builder
	builder.WriteString(kw)
	builder.WriteString(" ")
	builder.WriteString(name)
	builder.WriteString("(")
	builder.WriteString(StrObjSetPairs(f.Params, f.ParamSets))
	builder.WriteString(")")
	builder.WriteString(" ")
	builder.WriteString(f.RetSet.String())

	if len(f.DomFacts) == 0 && len(f.ThenFacts) == 0 {
		return builder.String()
	}
	builder.WriteString(glob.KeySymbolColon)
	builder.WriteByte('\n')

	if len(f.DomFacts) > 0 {
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(glob.KeywordDom, 1))
		builder.WriteString(glob.KeySymbolColon)
		builder.WriteByte('\n')
		domFactStrSlice := make([]string, len(f.DomFacts))
		for i := range len(f.DomFacts) {
			domFactStrSlice[i] = glob.SplitLinesAndAdd4NIndents(f.DomFacts[i].String(), 2)
		}
		builder.WriteString(strings.Join(domFactStrSlice, "\n"))
		builder.WriteByte('\n')
	}
	if len(f.ThenFacts) > 0 {
		// builder.WriteString(glob.SplitLinesAndAdd4NIndents(glob.KeywordThen, 1))
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(glob.KeySymbolRightArrow, 1))
		builder.WriteString(glob.KeySymbolColon)
		builder.WriteByte('\n')

		thenFactStrSlice := make([]string, len(f.ThenFacts))
		for i := range len(f.ThenFacts) {
			thenFactStrSlice[i] = glob.SplitLinesAndAdd4NIndents(f.ThenFacts[i].String(), 2)
		}
		builder.WriteString(strings.Join(thenFactStrSlice, "\n"))
	}

	return builder.String()
}

func (f *ClaimProveByContradictionStmt) String() string {
	return ClaimProve_ClaimProveByContradiction(glob.KeywordProveByContradiction, f.ClaimProveStmt.ToCheckFact, f.ClaimProveStmt.Proofs)
}

func (f *ClaimProveStmt) String() string {
	return ClaimProve_ClaimProveByContradiction(glob.KeywordProve, f.ToCheckFact, f.Proofs)
}

func ClaimProve_ClaimProveByContradiction(kw string, toCheckFact FactStmt, proofs []Stmt) string {
	var builder strings.Builder

	builder.WriteString(glob.KeywordClaim)
	builder.WriteString(glob.KeySymbolColon)
	builder.WriteByte('\n')

	builder.WriteString(glob.SplitLinesAndAdd4NIndents(toCheckFact.String(), 1))
	builder.WriteByte('\n')

	builder.WriteString(glob.SplitLinesAndAdd4NIndents(kw, 1))
	builder.WriteString(glob.KeySymbolColon)
	builder.WriteByte('\n')
	proofStrSlice := make([]string, len(proofs))
	for i := range len(proofs) {
		proofStrSlice[i] = glob.SplitLinesAndAdd4NIndents(proofs[i].String(), 2)
	}
	builder.WriteString(strings.Join(proofStrSlice, "\n"))
	return builder.String()
}

func (s *DefExistPropStmt) ToString(head string) string {
	var builder strings.Builder

	builder.WriteString(head)
	builder.WriteByte(' ')
	if len(s.ExistParams) > 0 {
		builder.WriteString(StrObjSetPairs(s.ExistParams, s.ExistParamSets))
	}
	builder.WriteString(" ")
	builder.WriteString(glob.KeywordSt)
	builder.WriteString(" ")
	builder.WriteString(s.DefBody.DefHeader.String())

	if len(s.DefBody.DomFactsOrNil) == 0 && len(s.DefBody.IffFactsOrNil) == 0 {
		return strings.TrimSuffix(builder.String(), glob.KeySymbolColon)
	}

	builder.WriteByte('\n')
	for _, domFact := range s.DefBody.DomFactsOrNil {
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(domFact.String(), 1))
		builder.WriteString("\n")
	}

	if len(s.DefBody.IffFactsOrNil) > 0 {
		indentNum := 1

		if len(s.DefBody.DomFactsOrNil) > 0 || len(s.DefBody.ImplicationFactsOrNil) > 0 {
			builder.WriteString(glob.SplitLinesAndAdd4NIndents("<=>:", 1))
			builder.WriteString("\n")
			indentNum = 2
		}

		iffFactStrSlice := make([]string, len(s.DefBody.IffFactsOrNil))
		for i := range len(s.DefBody.IffFactsOrNil) {
			iffFactStrSlice[i] = glob.SplitLinesAndAdd4NIndents(s.DefBody.IffFactsOrNil[i].String(), uint32(indentNum))
		}
		builder.WriteString(strings.Join(iffFactStrSlice, "\n"))
	}

	return builder.String()
}

func (s *DefExistPropStmt) String() string {
	return s.ToString(glob.KeywordExistProp)
}

func (l *UniFactStmt) StringWithLine() string {
	if l.GetLine() == 0 {
		return fmt.Sprintf("%s\na builtin fact", l.String())
	} else {
		return fmt.Sprintf("%s\non line %d", l.String(), l.GetLine())
	}
}

func (l *UniFactStmt) String() string {
	var builder strings.Builder

	builder.WriteString(glob.KeywordForall)
	builder.WriteString(" ")

	builder.WriteString(StrObjSetPairs(l.Params, l.ParamSets))

	builder.WriteString(":\n")
	if len(l.DomFacts) > 0 {
		domFactStrSlice := make([]string, len(l.DomFacts))
		for i := range len(l.DomFacts) {
			domFactStrSlice[i] = glob.SplitLinesAndAdd4NIndents(l.DomFacts[i].String(), 1)
		}
		builder.WriteString(strings.Join(domFactStrSlice, "\n"))

		builder.WriteByte('\n')
		builder.WriteString(glob.SplitLinesAndAdd4NIndents("=>:", 1))
		builder.WriteByte('\n')
		thenFactStrSlice := make([]string, len(l.ThenFacts))
		for i := range len(l.ThenFacts) {
			thenFactStrSlice[i] = glob.SplitLinesAndAdd4NIndents(l.ThenFacts[i].String(), 2)
		}
		builder.WriteString(strings.Join(thenFactStrSlice, "\n"))
	} else {
		thenFactStrSlice := make([]string, len(l.ThenFacts))
		for i := range len(l.ThenFacts) {
			thenFactStrSlice[i] = glob.SplitLinesAndAdd4NIndents(l.ThenFacts[i].String(), 1)
		}
		builder.WriteString(strings.Join(thenFactStrSlice, "\n"))
	}

	return builder.String()
}

func (l *UniFactWithIffStmt) String() string {
	var builder strings.Builder

	builder.WriteString(strings.TrimSuffix(l.UniFact.String(), "\n"))

	if l.IffFacts != nil && len(l.IffFacts) > 0 {
		builder.WriteByte('\n')
		builder.WriteString(glob.SplitLinesAndAdd4NIndents("<=>:", 1))
		builder.WriteByte('\n')
		iffFactStrSlice := make([]string, len(l.IffFacts))
		for i := range len(l.IffFacts) {
			iffFactStrSlice[i] = glob.SplitLinesAndAdd4NIndents(l.IffFacts[i].String(), 2)
		}
		builder.WriteString(strings.Join(iffFactStrSlice, "\n"))
	}
	return builder.String()
}

func (head DefHeader) StringWithoutColonAtEnd() string {
	var builder strings.Builder
	builder.WriteString(string(head.Name))
	builder.WriteString("(")

	builder.WriteString(StrObjSetPairs(head.Params, head.ParamSets))

	builder.WriteString(")")
	return builder.String()
}

func (head DefHeader) String() string {
	var builder strings.Builder
	builder.WriteString(head.StringWithoutColonAtEnd())
	builder.WriteString(glob.KeySymbolColon)
	return builder.String()
}

func (stmt *HaveObjStStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordHave)
	builder.WriteString(" ")
	builder.WriteString(strings.Join(stmt.ObjNames, ", "))
	builder.WriteByte(' ')
	builder.WriteString(glob.KeywordSt)
	builder.WriteString(" ")

	builder.WriteString(stmt.Fact.String())
	return builder.String()
}

func (f Atom) String() string {
	return string(f)
}

func TupleObjString(f *FnObj) string {
	var builder strings.Builder
	builder.WriteString("(")
	paramStrSlice := make([]string, len(f.Params))
	for i := range len(f.Params) {
		paramStrSlice[i] = f.Params[i].String()
	}
	builder.WriteString(strings.Join(paramStrSlice, ", "))
	builder.WriteString(")")
	return builder.String()
}

func IndexOptObjString(f *FnObj) string {
	var builder strings.Builder
	builder.WriteString(f.Params[0].String())
	builder.WriteString("[")
	builder.WriteString(f.Params[1].String())
	builder.WriteString("]")
	return builder.String()
}

func (f *FnObj) String() string {
	if IsFnSet(f) {
		return fnSetString(f)
	}

	if IsTupleFnObj(f) {
		return TupleObjString(f)
	}

	if IsIndexOptFnObj(f) {
		return IndexOptObjString(f)
	}

	if IsListSetObj(f) {
		paramStrSlice := make([]string, len(f.Params))
		for i := range len(f.Params) {
			paramStrSlice[i] = f.Params[i].String()
		}
		return fmt.Sprintf("%s%s%s", glob.KeySymbolLeftCurly, strings.Join(paramStrSlice, ", "), glob.KeySymbolRightCurly)
	}

	if IsSetBuilder(f) {
		return SetBuilderObjString(f)
	}

	if ok, str := hasBuiltinOptAndToString(f); ok {
		return str
	}

	var builder strings.Builder
	builder.WriteString(f.FnHead.String())
	builder.WriteString("(")
	paramStrSlice := make([]string, len(f.Params))
	for i := range len(f.Params) {
		paramStrSlice[i] = f.Params[i].String()
	}
	builder.WriteString(strings.Join(paramStrSlice, ", "))
	builder.WriteString(")")

	return builder.String()
}

func (stmt *ProveInEachCaseStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordProveInEachCase)
	builder.WriteString(":\n")
	builder.WriteString(glob.SplitLinesAndAdd4NIndents(stmt.OrFact.String(), 1))
	builder.WriteByte('\n')
	// builder.WriteString(glob.SplitLinesAndAdd4NIndents(glob.KeywordThen, 1))
	builder.WriteString(glob.SplitLinesAndAdd4NIndents(glob.KeySymbolRightArrow, 1))
	builder.WriteString(glob.KeySymbolColon)
	builder.WriteByte('\n')
	builder.WriteString(glob.SplitLinesAndAdd4NIndents(stmt.ThenFacts[0].String(), 2))
	builder.WriteByte('\n')
	// Handle last proof block
	if len(stmt.Proofs) > 0 {
		for i := range len(stmt.Proofs) {
			builder.WriteString(glob.SplitLinesAndAdd4NIndents(glob.KeywordProve, 1))
			builder.WriteString(glob.KeySymbolColon)
			builder.WriteByte('\n')

			if len(stmt.Proofs[i]) > 0 {
				for j := range len(stmt.Proofs[i]) - 1 {
					builder.WriteString(glob.SplitLinesAndAdd4NIndents(stmt.Proofs[i][j].String(), 2))
					builder.WriteByte('\n')
				}
				builder.WriteString(glob.SplitLinesAndAdd4NIndents(stmt.Proofs[i][len(stmt.Proofs[i])-1].String(), 2))
			}
			builder.WriteByte('\n')
		}
	}
	return strings.TrimSuffix(builder.String(), "\n")
}

func (stmt *ProveCaseByCaseStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordProveCaseByCase)
	builder.WriteString(":\n")
	for _, thenFact := range stmt.ThenFacts {
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(thenFact.String(), 1))
		builder.WriteByte('\n')
	}
	for _, proof := range stmt.Proofs {
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(glob.KeywordCase, 1))
		builder.WriteString(glob.KeySymbolColon)
		builder.WriteByte('\n')
		for _, fact := range proof {
			builder.WriteString(glob.SplitLinesAndAdd4NIndents(fact.String(), 2))
			builder.WriteByte('\n')
		}
		builder.WriteByte('\n')
	}
	return strings.TrimSuffix(builder.String(), "\n")
}

func (stmt *KnowPropStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordKnow)
	builder.WriteString(" ")
	builder.WriteString(stmt.Prop.String())
	return builder.String()
}

func fnSetString(f *FnObj) string {
	var builder strings.Builder
	builder.WriteString(f.FnHead.String())
	builder.WriteString(" ")
	builder.WriteString(f.Params[0].String())
	return builder.String()
}

func (stmt *OrStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordOr)
	builder.WriteString(glob.KeySymbolColon)
	builder.WriteByte('\n')
	orFactStrSlice := make([]string, len(stmt.Facts))
	for i, orFact := range stmt.Facts {
		orFactStrSlice[i] = glob.SplitLinesAndAdd4NIndents(orFact.String(), 1)
	}
	builder.WriteString(strings.Join(orFactStrSlice, "\n"))
	return builder.String()
}

func (stmt *ImportDirStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordImport)
	builder.WriteString(" ")
	builder.WriteString(stmt.AsPkgName)

	builder.WriteString(" ")
	builder.WriteString(glob.KeySymbolDoubleQuote)
	builder.WriteString(stmt.Path)
	builder.WriteString(glob.KeySymbolDoubleQuote)

	return builder.String()
}

func (stmt *ProveStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordProve)
	builder.WriteString(glob.KeySymbolColon)
	builder.WriteByte('\n')
	proofStrSlice := make([]string, len(stmt.Proof))
	for i, proof := range stmt.Proof {
		proofStrSlice[i] = glob.SplitLinesAndAdd4NIndents(proof.String(), 1)
	}
	builder.WriteString(strings.Join(proofStrSlice, "\n"))
	return builder.String()
}

func (stmt *DefFnStmt) String() string {
	return fnDefStmtStringGivenKw(glob.KeywordFn, stmt.FnTemplate, stmt.Name)
}

func (stmt *ImportFileStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordImport)
	builder.WriteString(" ")
	builder.WriteString(glob.KeySymbolDoubleQuote)
	builder.WriteString(stmt.Path)
	builder.WriteString(glob.KeySymbolDoubleQuote)
	return builder.String()
}

func (stmt *DefPropStmt) ToNamedUniFactString() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordImplication)
	builder.WriteString(stmt.DefHeader.String())
	builder.WriteString(glob.KeySymbolColon)
	builder.WriteByte('\n')

	var iffFactStrSlice []string
	for _, iffFact := range stmt.IffFactsOrNil {
		iffFactStrSlice = append(iffFactStrSlice, glob.SplitLinesAndAdd4NIndents(iffFact.String(), 2))
	}
	builder.WriteString(strings.Join(iffFactStrSlice, "\n"))
	builder.WriteByte('\n')

	var thenFactStrSlice []string
	builder.WriteString(glob.SplitLinesAndAdd4NIndents(glob.KeySymbolRightArrow, 1))
	builder.WriteString(glob.KeySymbolColon)
	builder.WriteByte('\n')
	for _, thenFact := range stmt.ImplicationFactsOrNil {
		thenFactStrSlice = append(thenFactStrSlice, glob.SplitLinesAndAdd4NIndents(thenFact.String(), 2))
	}
	builder.WriteString(strings.Join(thenFactStrSlice, "\n"))
	return builder.String()
}

func (stmt *ClaimImplicationStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordClaim)
	builder.WriteString(glob.KeySymbolColon)
	builder.WriteString("\n")
	builder.WriteString(glob.SplitLinesAndAdd4NIndents(stmt.Implication.ToProp().ToNamedUniFactString(), 1))
	builder.WriteByte('\n')
	proofStrSlice := make([]string, len(stmt.Proofs))
	for i, proof := range stmt.Proofs {
		proofStrSlice[i] = glob.SplitLinesAndAdd4NIndents(proof.String(), 1)
	}
	builder.WriteString(strings.Join(proofStrSlice, "\n"))
	return builder.String()
}

func (stmt *ClaimExistPropStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordClaim)
	builder.WriteString(glob.KeySymbolColon)
	builder.WriteString("\n")
	builder.WriteString(glob.SplitLinesAndAdd4NIndents(stmt.ExistPropWithoutDom.String(), 1))
	builder.WriteByte('\n')
	proofStrSlice := make([]string, len(stmt.Proofs))
	for i, proof := range stmt.Proofs {
		proofStrSlice[i] = glob.SplitLinesAndAdd4NIndents(proof.String(), 1)
	}
	builder.WriteString(strings.Join(proofStrSlice, "\n"))
	return builder.String()
}

func (stmt *ProveByEnumStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordProveByEnum)
	builder.WriteString(glob.KeySymbolColon)
	builder.WriteByte('\n')
	builder.WriteString(glob.SplitLinesAndAdd4NIndents(stmt.Fact.String(), 1))
	builder.WriteByte('\n')
	if len(stmt.Proof) > 0 {
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(glob.KeywordProve, 1))
		builder.WriteString(glob.KeySymbolColon)
		builder.WriteByte('\n')

		proofStrSlice := make([]string, len(stmt.Proof))
		for i, proof := range stmt.Proof {
			proofStrSlice[i] += glob.SplitLinesAndAdd4NIndents(proof.String(), 2)
			proofStrSlice[i] += "\n"
		}
		builder.WriteString(strings.Join(proofStrSlice, "\n"))
	}
	return builder.String()
}

func (stmt *HaveObjFromCartSetStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordHave)
	builder.WriteString(" ")
	builder.WriteString(stmt.ObjName)
	builder.WriteString(" ")
	builder.WriteString(stmt.CartSet.String())
	builder.WriteString(" ")
	builder.WriteString(glob.KeySymbolEqual)
	builder.WriteString(" ")
	builder.WriteString(stmt.EqualTo.String())
	return builder.String()
}

// func (stmt *NamedUniFactStmt) String() string {
// 	var builder strings.Builder
// 	builder.WriteString(glob.KeySymbolAt)
// 	builder.WriteString(" ")
// 	builder.WriteString(stmt.DefPropStmt.String())
// 	return builder.String()
// }

func (stmt *EqualsFactStmt) String() string {
	var builder strings.Builder
	factStrSlice := make([]string, len(stmt.Params))
	for i := range len(stmt.Params) {
		factStrSlice[i] = stmt.Params[i].String()
	}
	builder.WriteString(strings.Join(factStrSlice, " = "))
	return builder.String()
}

func (stmt *KnowExistPropStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordKnow)
	builder.WriteString(" ")
	builder.WriteString(stmt.ExistProp.String())
	return builder.String()
}

// func (stmt *LatexStmt) String() string {
// 	return stmt.Comment
// }

func (stmt *FnTemplateDefStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordFnSet)
	builder.WriteString(" ")
	builder.WriteString(stmt.TemplateDefHeader.String())
	builder.WriteString("\n")

	if len(stmt.TemplateDomFacts) > 0 {
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(glob.KeywordDom, 1))
		builder.WriteString(glob.KeySymbolColon)
		builder.WriteByte('\n')
		domFactStrSlice := make([]string, len(stmt.TemplateDomFacts))
		for i := range len(stmt.TemplateDomFacts) {
			domFactStrSlice[i] = glob.SplitLinesAndAdd4NIndents(stmt.TemplateDomFacts[i].String(), 2)
		}
		builder.WriteString(strings.Join(domFactStrSlice, "\n"))
		builder.WriteByte('\n')
	}

	builder.WriteString(glob.SplitLinesAndAdd4NIndents(NewDefFnStmt("", NewFnTStruct(stmt.Fn.Params, stmt.Fn.ParamSets, stmt.Fn.RetSet, stmt.Fn.DomFacts, stmt.Fn.ThenFacts, stmt.Line), stmt.Line).String(), 1))

	return builder.String()
}

func (stmt *ClearStmt) String() string {
	return glob.KeywordClear
}

func (stmt *DoNothingStmt) String() string {
	return glob.KeywordDoNothing
}

func (stmt *InlineFactsStmt) String() string {
	strSlice := make([]string, len(stmt.Facts))
	for i := range len(stmt.Facts) {
		strSlice[i] = stmt.Facts[i].String()
	}
	return strings.Join(strSlice, "\n")
}

func (stmt *ProveByInductionStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordProveByInduction)
	builder.WriteString("(")
	builder.WriteString(stmt.Fact.String())
	builder.WriteString(", ")
	builder.WriteString(stmt.Param)
	builder.WriteString(", ")
	builder.WriteString(stmt.Start.String())
	builder.WriteString(")")
	return builder.String()
}

func (stmt *HaveObjEqualStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordHave)
	builder.WriteString(" ")
	nameSlice := make([]string, len(stmt.ObjNames))
	for i := range len(stmt.ObjNames) {
		nameSlice[i] = fmt.Sprintf("%s %s", stmt.ObjNames[i], stmt.ObjSets[i])
	}
	builder.WriteString(strings.Join(nameSlice, ", "))
	builder.WriteString(" ")
	builder.WriteString(glob.KeySymbolEqual)
	builder.WriteString(" ")
	equalToSlice := make([]string, len(stmt.ObjEqualTos))
	for i := range len(stmt.ObjEqualTos) {
		equalToSlice[i] = stmt.ObjEqualTos[i].String()
	}
	builder.WriteString(strings.Join(equalToSlice, ", "))
	return builder.String()
}

func (stmt *HaveFnEqualStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordHave)
	builder.WriteString(" ")
	builder.WriteString(glob.KeywordFn)
	builder.WriteString(" ")
	builder.WriteString(stmt.DefHeader.StringWithoutColonAtEnd())
	builder.WriteString(" ")
	builder.WriteString(stmt.RetSet.String())
	builder.WriteString(" ")
	builder.WriteString(glob.KeySymbolEqual)
	builder.WriteString(" ")
	builder.WriteString(stmt.EqualTo.String())

	return builder.String()
}

func (stmt *HaveFnStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordHave)
	builder.WriteString(" ")
	builder.WriteString(glob.KeywordFn)
	builder.WriteString(glob.KeySymbolColon)
	builder.WriteString("\n")
	builder.WriteString(glob.SplitLinesAndAdd4NIndents(stmt.DefFnStmt.String(), 1))
	builder.WriteString("\n")
	for _, proof := range stmt.Proofs {
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(proof.String(), 1))
		builder.WriteByte('\n')
	}
	builder.WriteString(glob.SplitLinesAndAdd4NIndents(fmt.Sprintf("%s %s", glob.KeywordHave, stmt.HaveObjSatisfyFn.String()), 1))
	return builder.String()
}

func (stmt *HaveFnCaseByCaseStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordHave)
	builder.WriteString(" ")
	builder.WriteString(glob.KeywordFn)
	builder.WriteString(glob.KeySymbolColon)
	builder.WriteString("\n")
	builder.WriteString(glob.SplitLinesAndAdd4NIndents(stmt.DefFnStmt.String(), 1))
	builder.WriteString("\n")
	for i := range len(stmt.CaseByCaseFacts) {
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(glob.KeywordCase, 1))
		builder.WriteString(" ")
		builder.WriteString(stmt.CaseByCaseFacts[i].String())
		builder.WriteString(glob.KeySymbolColon)
		builder.WriteByte('\n')
		if i < len(stmt.Proofs) {
			for _, proofStmt := range stmt.Proofs[i] {
				builder.WriteString(glob.SplitLinesAndAdd4NIndents(proofStmt.String(), 2))
				builder.WriteByte('\n')
			}
		}
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(glob.KeywordHave, 1))
		builder.WriteString(" ")
		if i < len(stmt.EqualToObjs) {
			builder.WriteString(stmt.EqualToObjs[i].String())
		}
		builder.WriteByte('\n')
	}
	return strings.TrimSuffix(builder.String(), "\n")
}

func (objSlice ObjSlice) String() string {
	output := make([]string, len(objSlice))
	for i, param := range objSlice {
		output[i] = param.String()
	}
	return strings.Join(output, ", ")
}

func (params StrSlice) String() string {
	output := make([]string, len(params))
	copy(output, params)
	return strings.Join(output, ", ")
}

func (fnTStruct *FnTStruct) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordFn)
	builder.WriteString(" ")
	builder.WriteString(glob.KeySymbolLeftBrace)
	pair := make([]string, len(fnTStruct.Params))
	for i, param := range fnTStruct.Params {
		pair[i] = fmt.Sprintf("%s %s", param, fnTStruct.ParamSets[i].String())
	}
	builder.WriteString(strings.Join(pair, ", "))
	builder.WriteString(glob.KeySymbolRightBrace)
	builder.WriteString(" ")
	builder.WriteString(fnTStruct.RetSet.String())
	builder.WriteString(glob.KeySymbolColon)
	builder.WriteByte('\n')
	if len(fnTStruct.DomFacts) > 0 {
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(glob.KeywordDom, 1))
		builder.WriteByte('\n')
		for _, fact := range fnTStruct.DomFacts {
			builder.WriteString(glob.SplitLinesAndAdd4NIndents(fact.String(), 2))
			builder.WriteByte('\n')
		}
	}
	if len(fnTStruct.ThenFacts) > 0 {
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(glob.KeySymbolRightArrow, 1))
		builder.WriteByte('\n')
		for _, fact := range fnTStruct.ThenFacts {
			builder.WriteString(glob.SplitLinesAndAdd4NIndents(fact.String(), 2))
			builder.WriteByte('\n')
		}
	}
	return builder.String()
}

// func (stmt *MarkdownStmt) String() string {
// 	return stmt.Markdown
// }

func (stmt *ClaimIffStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordClaim)
	builder.WriteString(glob.KeySymbolColon)
	builder.WriteByte('\n')
	builder.WriteString(glob.SplitLinesAndAdd4NIndents(stmt.UniFactWithIffStmt.String(), 1))
	builder.WriteByte('\n')
	builder.WriteString(glob.SplitLinesAndAdd4NIndents(glob.KeywordProve, 1))
	builder.WriteString(glob.SplitLinesAndAdd4NIndents(glob.KeySymbolColon, 1))
	builder.WriteByte('\n')
	for _, proof := range stmt.ProofThenToIff {
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(proof.String(), 2))
		builder.WriteByte('\n')
	}
	builder.WriteString(glob.SplitLinesAndAdd4NIndents(glob.KeywordProve, 1))
	builder.WriteString(glob.SplitLinesAndAdd4NIndents(glob.KeySymbolColon, 1))
	builder.WriteByte('\n')
	for _, proof := range stmt.ProofIffToThen {
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(proof.String(), 2))
		builder.WriteByte('\n')
	}
	return builder.String()
}

func (stmt *ProveForStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordProveFor)
	builder.WriteString(" ")
	builder.WriteString(stmt.Param)
	builder.WriteString(" ")
	builder.WriteString(glob.FuncFactPrefix)
	builder.WriteString(glob.KeywordIn)
	builder.WriteString(" ")
	if stmt.IsProveIRange {
		builder.WriteString(glob.KeywordRange)
	} else {
		builder.WriteString(glob.KeywordClosedRange)
	}
	builder.WriteString("(")
	builder.WriteString(stmt.Left.String())
	builder.WriteString(", ")
	builder.WriteString(stmt.Right.String())
	builder.WriteString(")")
	builder.WriteString(":")

	hasDom := len(stmt.DomFacts) > 0
	hasProve := len(stmt.Proofs) > 0

	if hasDom {
		// First section is dom: format is dom:, =>:, (optional) prove:
		builder.WriteString("\n    dom:\n")
		for _, fact := range stmt.DomFacts {
			builder.WriteString("        ")
			builder.WriteString(fact.String())
			builder.WriteString("\n")
		}
		if len(stmt.ThenFacts) > 0 {
			builder.WriteString("    =>:\n")
			for _, fact := range stmt.ThenFacts {
				builder.WriteString("        ")
				builder.WriteString(fact.String())
				builder.WriteString("\n")
			}
		}
		if hasProve {
			builder.WriteString("    prove:\n")
			for _, proof := range stmt.Proofs {
				builder.WriteString(glob.SplitLinesAndAdd4NIndents(proof.String(), 2))
				builder.WriteString("\n")
			}
		}
	} else {
		// First section is not dom
		if hasProve {
			// Case 2: =>:, prove: (no dom section)
			if len(stmt.ThenFacts) > 0 {
				builder.WriteString("\n    =>:\n")
				for _, fact := range stmt.ThenFacts {
					builder.WriteString("        ")
					builder.WriteString(fact.String())
					builder.WriteString("\n")
				}
			}
			builder.WriteString("    prove:\n")
			for _, proof := range stmt.Proofs {
				builder.WriteString(glob.SplitLinesAndAdd4NIndents(proof.String(), 2))
				builder.WriteString("\n")
			}
		} else {
			// Case 3: No prove: format is direct fact statements (no =>:)
			if len(stmt.ThenFacts) > 0 {
				builder.WriteString("\n")
				for _, fact := range stmt.ThenFacts {
					builder.WriteString("    ")
					builder.WriteString(fact.String())
					builder.WriteString("\n")
				}
			}
		}
	}
	return builder.String()
}

func (stmt *ProveImplicationStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordProveImplication)
	builder.WriteString(" ")
	builder.WriteString(stmt.ImplicationName)
	if len(stmt.Params) > 0 {
		builder.WriteString("(")
		builder.WriteString(strings.Join(stmt.Params, ", "))
		builder.WriteString(")")
	}
	builder.WriteString(":")

	hasProve := len(stmt.Proof) > 0

	if hasProve {
		// Case 1: =>:, prove: format
		if len(stmt.ImplicationFact) > 0 {
			builder.WriteString("\n    =>:\n")
			for _, fact := range stmt.ImplicationFact {
				builder.WriteString("        ")
				builder.WriteString(fact.String())
				builder.WriteString("\n")
			}
		}
		builder.WriteString("    prove:\n")
		for _, proof := range stmt.Proof {
			builder.WriteString(glob.SplitLinesAndAdd4NIndents(proof.String(), 2))
			builder.WriteString("\n")
		}
	} else {
		// Case 2: All are implications, no prove section
		if len(stmt.ImplicationFact) > 0 {
			builder.WriteString("\n")
			for _, fact := range stmt.ImplicationFact {
				builder.WriteString("    ")
				builder.WriteString(fact.String())
				builder.WriteString("\n")
			}
		}
	}
	return builder.String()
}

func (stmt *ImplicationStmt) String() string {
	var builder strings.Builder

	builder.WriteString(glob.KeywordImplication)
	builder.WriteByte(' ')
	builder.WriteString(stmt.DefHeader.String())

	if len(stmt.DomFacts) == 0 && len(stmt.ImplicationFacts) == 0 {
		return strings.TrimSuffix(builder.String(), glob.KeySymbolColon)
	}

	builder.WriteByte('\n')
	if len(stmt.DomFacts) > 0 {
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(glob.KeywordDom, 1))
		builder.WriteString(glob.KeySymbolColon)
		builder.WriteByte('\n')
		domFactStrSlice := make([]string, len(stmt.DomFacts))
		for i := range len(stmt.DomFacts) {
			domFactStrSlice[i] = glob.SplitLinesAndAdd4NIndents(stmt.DomFacts[i].String(), 2)
		}
		builder.WriteString(strings.Join(domFactStrSlice, "\n"))
		builder.WriteByte('\n')
	}

	if len(stmt.ImplicationFacts) > 0 {
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(glob.KeySymbolRightArrow, 1))
		builder.WriteString(glob.KeySymbolColon)
		builder.WriteByte('\n')
		implicationFactStrSlice := make([]string, len(stmt.ImplicationFacts))
		for i := range len(stmt.ImplicationFacts) {
			implicationFactStrSlice[i] = glob.SplitLinesAndAdd4NIndents(stmt.ImplicationFacts[i].String(), 2)
		}
		builder.WriteString(strings.Join(implicationFactStrSlice, "\n"))
		builder.WriteByte('\n')
	}

	return builder.String()
}

func ProveIsCertainPropStmtString(kw string, prop Atom, params []string, proofs []Stmt) string {
	var builder strings.Builder
	builder.WriteString(kw)
	builder.WriteString("(")
	builder.WriteString(prop.String())
	builder.WriteString(")")
	builder.WriteString(glob.KeySymbolColon)
	builder.WriteByte('\n')
	for _, proof := range proofs {
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(proof.String(), 1))
		builder.WriteByte('\n')
	}
	return builder.String()
}

func (stmt *ProveIsTransitivePropStmt) String() string {
	return ProveIsCertainPropStmtString(glob.KeywordProveIsTransitiveProp, stmt.Prop, stmt.Params, stmt.Proofs)
}

func (stmt *ProveIsCommutativePropStmt) String() string {
	var builder strings.Builder
	builder.WriteString(stmt.SpecFact.String())
	builder.WriteString(glob.KeySymbolColon)
	builder.WriteByte('\n')

	builder.WriteString(glob.SplitLinesAndAdd4NIndents(glob.KeywordProve, 1))
	builder.WriteString(glob.KeySymbolColon)
	builder.WriteByte('\n')
	for _, proof := range stmt.Proofs {
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(proof.String(), 2))
		builder.WriteByte('\n')
	}

	builder.WriteString(glob.SplitLinesAndAdd4NIndents(glob.KeywordProve, 1))
	builder.WriteString(glob.KeySymbolColon)
	builder.WriteByte('\n')
	for _, proof := range stmt.ProofsRightToLeft {
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(proof.String(), 2))
		builder.WriteByte('\n')
	}

	return builder.String()
}

func (stmt *ProveAlgoIfStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordIf)
	builder.WriteString(" ")
	conditionStrSlice := make([]string, len(stmt.Conditions))
	for i, fact := range stmt.Conditions {
		conditionStrSlice[i] = fact.String()
	}
	builder.WriteString(strings.Join(conditionStrSlice, ", "))
	builder.WriteString(" ")
	builder.WriteString(glob.KeySymbolColon)
	builder.WriteByte('\n')
	for _, fact := range stmt.ThenStmts {
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(fact.String(), 1))
		builder.WriteByte('\n')
	}
	return builder.String()
}

func (stmt *AlgoIfStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordIf)
	builder.WriteString(" ")
	conditionStrSlice := make([]string, len(stmt.Conditions))
	for i, fact := range stmt.Conditions {
		conditionStrSlice[i] = fact.String()
	}
	builder.WriteString(strings.Join(conditionStrSlice, ", "))
	builder.WriteString(" ")
	builder.WriteString(glob.KeySymbolColon)
	builder.WriteByte('\n')
	for _, fact := range stmt.ThenStmts {
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(fact.String(), 1))
		builder.WriteByte('\n')
	}
	return builder.String()
}

func (stmt *AlgoReturnStmt) String() string {
	return fmt.Sprintf("%s %s", glob.KeywordReturn, stmt.Value.String())
}

func (stmt *DefAlgoStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordAlgo)
	builder.WriteString(" ")
	builder.WriteString(stmt.FuncName)
	builder.WriteString("(")
	builder.WriteString(strings.Join(stmt.Params, ", "))
	builder.WriteString(")")
	builder.WriteString(glob.KeySymbolColon)
	builder.WriteByte('\n')
	strSlice := make([]string, len(stmt.Stmts))
	for i, stmt := range stmt.Stmts {
		strSlice[i] = stmt.String()
	}
	builder.WriteString(strings.Join(strSlice, "\n"))
	return builder.String()
}

func StmtStrSliceJoin(stmts []Stmt, joinWith string) string {
	var builder strings.Builder
	strSlice := make([]string, len(stmts))
	for i, stmt := range stmts {
		strSlice[i] = stmt.String()
	}
	builder.WriteString(strings.Join(strSlice, joinWith))
	return builder.String()
}

func StmtStrSliceJoinWithNewlineWithIndents(stmts []Stmt, indents uint32) string {
	var builder strings.Builder
	strSlice := make([]string, len(stmts))
	for i, stmt := range stmts {
		strSlice[i] = glob.SplitLinesAndAdd4NIndents(stmt.String(), indents)
	}
	builder.WriteString(strings.Join(strSlice, "\n"))
	return builder.String()
}

func FactStmtStrSliceJoinWithNewlineWithIndents(stmts []FactStmt, indents uint32) string {
	var builder strings.Builder
	strSlice := make([]string, len(stmts))
	for i, stmt := range stmts {
		strSlice[i] = glob.SplitLinesAndAdd4NIndents(stmt.String(), indents)
	}
	builder.WriteString(strings.Join(strSlice, "\n"))
	return builder.String()
}

func AlgoStmtStrSliceJoinWithNewlineWithIndents(stmts []Stmt, indents uint32) string {
	var builder strings.Builder
	strSlice := make([]string, len(stmts))
	for i, stmt := range stmts {
		strSlice[i] = glob.SplitLinesAndAdd4NIndents(stmt.String(), indents)
	}
	builder.WriteString(strings.Join(strSlice, "\n"))
	return builder.String()
}

func (stmt *EvalStmt) String() string {
	return fmt.Sprintf("%s(%s)", glob.KeywordEval, stmt.ObjToEval.String())
}

func (stmt *DefProveAlgoStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordProveAlgo)
	builder.WriteString(" ")
	builder.WriteString(stmt.ProveAlgoName)
	builder.WriteString("(")
	builder.WriteString(stmt.Params.String())
	builder.WriteString(")")
	builder.WriteString(glob.KeySymbolColon)
	builder.WriteByte('\n')
	strSlice := make([]string, len(stmt.Stmts))
	for i, stmt := range stmt.Stmts {
		strSlice[i] = stmt.String()
	}
	builder.WriteString(strings.Join(strSlice, "\n"))
	return builder.String()
}

func (stmt *ByStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordBy)
	builder.WriteString(" ")
	builder.WriteString(stmt.ProveAlgoName)
	builder.WriteString("(")
	builder.WriteString(stmt.Params.String())
	builder.WriteString(")")
	return builder.String()
}

func (stmt *ProveAlgoReturnStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordReturn)
	if len(stmt.Facts) == 0 {
		return builder.String()
	}

	// Check if it's a single inline fact (no colon case) or multiple facts (colon case)
	if len(stmt.Facts) == 1 {
		// Single inline fact
		builder.WriteString(" ")
		builder.WriteString(stmt.Facts[0].String())
	} else {
		// Multiple facts from body
		builder.WriteString(glob.KeySymbolColon)
		for i, fact := range stmt.Facts {
			if i > 0 {
				builder.WriteString("\n")
			}
			builder.WriteString(fact.String())
		}
	}
	return builder.String()
}

func (stmt *HaveFnEqualCaseByCaseStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordHave)
	builder.WriteString(" ")
	builder.WriteString(glob.KeywordFn)
	builder.WriteString(" ")
	builder.WriteString(stmt.DefHeader.StringWithoutColonAtEnd())
	builder.WriteString(" ")
	builder.WriteString(stmt.RetSet.String())
	builder.WriteString(" ")
	builder.WriteString(glob.KeySymbolEqual)
	builder.WriteString(glob.KeySymbolColon)
	builder.WriteByte('\n')
	for i, fact := range stmt.CaseByCaseFacts {
		builder.WriteString("    ")
		builder.WriteString(glob.KeywordCase)
		builder.WriteString(" ")
		builder.WriteString(fact.String())
		builder.WriteString(glob.KeySymbolColon)
		builder.WriteString(" ")
		builder.WriteString(stmt.CaseByCaseEqualTo[i].String())
		builder.WriteByte('\n')
	}
	return strings.TrimSpace(builder.String())
}

func SetBuilderObjString(f *FnObj) string {
	// Convert FnObj to SetBuilderStruct for easier processing
	setBuilder, err := f.ToSetBuilderStruct()
	if err != nil {
		// Fallback to basic representation if conversion fails
		return fmt.Sprintf("%s%s %s%s (parse error: %s)", glob.KeySymbolLeftCurly, f.Params[0].String(), f.Params[1].String(), glob.KeySymbolColon, err.Error())
	}

	var builder strings.Builder
	builder.WriteString(glob.KeySymbolLeftCurly)
	builder.WriteString(setBuilder.Param)
	builder.WriteByte(' ')
	builder.WriteString(setBuilder.ParentSet.String())
	builder.WriteString(glob.KeySymbolColon)

	// Convert facts to strings
	if len(setBuilder.Facts) > 0 {
		factStrings := make([]string, len(setBuilder.Facts))
		for i, fact := range setBuilder.Facts {
			factStrings[i] = fact.String()
		}
		builder.WriteByte(' ')
		builder.WriteString(strings.Join(factStrings, ", "))
	}

	builder.WriteString(glob.KeySymbolRightCurly)
	return builder.String()
}
