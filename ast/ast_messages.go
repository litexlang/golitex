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
// Litex website: https://litexlang.org
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

	builder.WriteString(glob.KeywordKnow)
	builder.WriteString(glob.KeySymbolColon)
	builder.WriteByte('\n')

	factStrSlice := make([]string, len(stmt.Facts))
	for i := range len(stmt.Facts) {
		factStrSlice[i] = glob.SplitLinesAndAdd4NIndents(stmt.Facts[i].String(), 1)
	}
	builder.WriteString(strings.Join(factStrSlice, "\n"))
	return builder.String()
}

func (stmt *SpecFactStmt) String() string {
	if stmt.IsExist_St_Fact() {
		return exist_st_FactString(stmt)
	} else {
		return pureFactString(stmt)
	}
}

func pureFactString(stmt *SpecFactStmt) string {
	var builder strings.Builder

	if stmt.TypeEnum == FalsePure {
		builder.WriteString(glob.KeywordNot)
		builder.WriteByte(' ')
	}

	if glob.IsKeySymbol(string(stmt.PropName)) {
		builder.WriteString(relaFactWithoutNotString(stmt))
	} else {
		builder.WriteString(glob.FuncFactPrefix)
		builder.WriteString(stmt.PropName.String())
		builder.WriteByte('(')

		builder.WriteString(fcSliceString(stmt.Params))
		builder.WriteByte(')')
	}
	return builder.String()
}

func relaFactWithoutNotString(stmt *SpecFactStmt) string {
	var builder strings.Builder

	builder.WriteString(stmt.Params[0].String())
	builder.WriteByte(' ')
	builder.WriteString(stmt.PropName.String())
	builder.WriteByte(' ')
	builder.WriteString(stmt.Params[1].String())

	return builder.String()
}

func strFcSetPairs(objs []string, objSets []Fc) string {
	pairStrSlice := make([]string, len(objs))
	for i := range len(objs) {
		pairStrSlice[i] = fmt.Sprintf("%s %v", objs[i], objSets[i])
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

	builder.WriteString(fcSliceString(existParams))
	builder.WriteString(" ")
	builder.WriteString(glob.KeywordSt)
	builder.WriteString(" ")
	builder.WriteString(NewSpecFactStmt(TruePure, stmt.PropName, factParams).String())

	return builder.String()
}

func (stmt *DefObjStmt) String() string {
	var builder strings.Builder

	builder.WriteString(glob.KeywordObj)
	builder.WriteString(" ")
	builder.WriteString(strFcSetPairs(stmt.Objs, stmt.ObjSets))

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
	builder.WriteString(strFcSetPairs(stmt.Objs, stmt.ObjSets))

	return builder.String()
}

func (fact *DefPropStmt) String() string {
	var builder strings.Builder

	builder.WriteString(glob.KeywordProp)
	builder.WriteByte(' ')
	builder.WriteString(fact.DefHeader.String())

	if len(fact.DomFacts) == 0 && len(fact.IffFacts) == 0 {
		return strings.TrimSuffix(builder.String(), glob.KeySymbolColon)
	}

	builder.WriteByte('\n')
	if len(fact.DomFacts) > 0 {
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(glob.KeywordDom, 1))
		builder.WriteString(glob.KeySymbolColon)
		builder.WriteByte('\n')
		domFactStrSlice := make([]string, len(fact.DomFacts))
		for i := range len(fact.DomFacts) {
			domFactStrSlice[i] = glob.SplitLinesAndAdd4NIndents(fact.DomFacts[i].String(), 2)
		}
		builder.WriteString(strings.Join(domFactStrSlice, "\n"))
		builder.WriteByte('\n')
	}

	if len(fact.IffFacts) > 0 {
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(glob.KeywordIff, 1))
		builder.WriteString(glob.KeySymbolColon)
		builder.WriteByte('\n')
		iffFactStrSlice := make([]string, len(fact.IffFacts))
		for i := range len(fact.IffFacts) {
			iffFactStrSlice[i] = glob.SplitLinesAndAdd4NIndents(fact.IffFacts[i].String(), 2)
		}
		builder.WriteString(strings.Join(iffFactStrSlice, "\n"))
	}

	return builder.String()

}

func fnDefStmtStringGivenKw(kw string, f *FnTemplateStmt) string {
	var builder strings.Builder
	builder.WriteString(kw)
	builder.WriteString(" ")
	builder.WriteString(f.Name)
	builder.WriteString("(")
	builder.WriteString(fcSliceString(f.ParamSets))
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
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(glob.KeywordThen, 1))
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

func (f *FnTemplateStmt) String() string {
	return fnDefStmtStringGivenKw(glob.KeywordFn, f)
}

func (f *DefFnTemplateStmt) String() string {
	return fnDefStmtStringGivenKw(glob.KeywordFnTemplate, &f.FnTemplateStmt)
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

func (s *DefExistPropStmt) String() string {
	var builder strings.Builder

	builder.WriteString(glob.KeywordExistProp)
	builder.WriteByte(' ')
	if len(s.ExistParams) > 0 {
		builder.WriteString(strings.Join(s.ExistParams, ", "))
	}
	builder.WriteString(" ")
	builder.WriteString(glob.KeywordSt)
	builder.WriteString(" ")
	builder.WriteString(s.DefBody.DefHeader.String())

	if len(s.DefBody.DomFacts) == 0 && len(s.DefBody.IffFacts) == 0 {
		return strings.TrimSuffix(builder.String(), glob.KeySymbolColon)
	}

	builder.WriteByte('\n')
	for _, domFact := range s.DefBody.DomFacts {
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(domFact.String(), 1))
		builder.WriteString("\n")
	}

	if len(s.DefBody.IffFacts) > 0 {
		builder.WriteString(glob.SplitLinesAndAdd4NIndents("iff:", 1))
		builder.WriteString("\n")

		iffFactStrSlice := make([]string, len(s.DefBody.IffFacts))
		for i := range len(s.DefBody.IffFacts) {
			iffFactStrSlice[i] = glob.SplitLinesAndAdd4NIndents(s.DefBody.IffFacts[i].String(), 2)
		}
		builder.WriteString(strings.Join(iffFactStrSlice, "\n"))
	}

	return builder.String()
}

func (l *UniFactStmt) String() string {
	var builder strings.Builder

	builder.WriteString(glob.KeywordForall)
	builder.WriteString(" ")

	builder.WriteString(strFcSetPairs(l.Params, l.ParamSets))

	builder.WriteString(":\n")
	if len(l.DomFacts) > 0 {
		domFactStrSlice := make([]string, len(l.DomFacts))
		for i := range len(l.DomFacts) {
			domFactStrSlice[i] = glob.SplitLinesAndAdd4NIndents(l.DomFacts[i].String(), 1)
		}
		builder.WriteString(strings.Join(domFactStrSlice, "\n"))

		builder.WriteByte('\n')
		builder.WriteString(glob.SplitLinesAndAdd4NIndents("then:", 1))
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
		builder.WriteString(glob.SplitLinesAndAdd4NIndents("iff:", 1))
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
	builder.WriteString(head.Name)
	builder.WriteString("(")

	builder.WriteString(strFcSetPairs(head.Params, head.ParamSets))

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

func (f FcAtom) String() string {
	return string(f)
}

func (f *FcFn) String() string {
	if IsFnSet(f) {
		return fnSetString(f)
	}

	// if IsFcAtomEqualToGivenString_WithoutColonColon(f.FnHead, glob.KeySymbolDot) {
	if IsFcAtomAndEqualToStr(f.FnHead, glob.KeySymbolDot) {
		return fmt.Sprintf("%v.%v", f.Params[0], f.Params[1])
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
	builder.WriteString(glob.SplitLinesAndAdd4NIndents(glob.KeywordThen, 1))
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

func (stmt *KnowPropStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordKnow)
	builder.WriteString(" ")
	builder.WriteString(stmt.Prop.String())
	return builder.String()
}

func (stmt *KnowExistPropStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordKnow)
	builder.WriteString(" ")
	builder.WriteString(stmt.ExistProp.String())
	return builder.String()
}

func fnSetString(f *FcFn) string {
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

	builder.WriteString(glob.KeySymbolDoubleQuote)
	builder.WriteString(stmt.Path)
	builder.WriteString(glob.KeySymbolDoubleQuote)
	builder.WriteString(" ")

	if stmt.AsPkgName != "" {
		builder.WriteString(glob.KeywordAs)
		builder.WriteString(" ")
		builder.WriteString(stmt.AsPkgName)
	}

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
	return fnDefStmtStringGivenKw(glob.KeywordFn, &stmt.FnTemplateStmt)
}

func (stmt *EnumStmt) String() string {
	var builder strings.Builder
	builder.WriteString(stmt.CurSet.String())
	builder.WriteString(" ")
	builder.WriteString(glob.KeySymbolColonEqual)
	builder.WriteString(" ")
	builder.WriteString(glob.KeySymbolLeftCurly)
	itemsStrSlice := make([]string, len(stmt.Items))
	for i := range len(stmt.Items) {
		itemsStrSlice[i] = stmt.Items[i].String()
	}
	builder.WriteString(strings.Join(itemsStrSlice, ", "))
	builder.WriteString(glob.KeySymbolRightCurly)
	return builder.String()
}

// func (stmt *ImportGloballyStmt) String() string {
// 	var builder strings.Builder
// 	builder.WriteString(glob.KeywordImportGlobally)
// 	builder.WriteString(" ")
// 	builder.WriteString(glob.KeySymbolDoubleQuote)
// 	builder.WriteString(stmt.Path)
// 	builder.WriteString(glob.KeySymbolDoubleQuote)
// 	return builder.String()
// }

func (stmt *ImportFileStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordImport)
	builder.WriteString(" ")
	builder.WriteString(glob.KeySymbolDoubleQuote)
	builder.WriteString(stmt.Path)
	builder.WriteString(glob.KeySymbolDoubleQuote)
	return builder.String()
}

func (stmt *ClaimPropStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordClaim)
	builder.WriteString(glob.KeySymbolColon)
	builder.WriteString("\n")
	builder.WriteString(glob.SplitLinesAndAdd4NIndents(stmt.Prop.String(), 1))
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
	builder.WriteString(glob.SplitLinesAndAdd4NIndents(stmt.ExistProp.String(), 1))
	builder.WriteByte('\n')
	proofStrSlice := make([]string, len(stmt.Proofs))
	for i, proof := range stmt.Proofs {
		proofStrSlice[i] = glob.SplitLinesAndAdd4NIndents(proof.String(), 1)
	}
	builder.WriteString(strings.Join(proofStrSlice, "\n"))
	return builder.String()
}

func (stmt *ProveByMathInductionStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordProveByMathInduction)
	builder.WriteString(" ")
	builder.WriteString(stmt.PropName.String())
	builder.WriteString(" ")
	builder.WriteString(stmt.Start.String())
	return builder.String()
}

func (stmt *IntensionalSetStmt) String() string {
	var builder strings.Builder
	builder.WriteString(stmt.CurSet.String())
	builder.WriteString(" ")
	builder.WriteString(glob.KeySymbolColonEqual)
	builder.WriteString(" ")
	builder.WriteString(stmt.Param)
	builder.WriteString(" ")
	builder.WriteString(stmt.ParentSet.String())
	builder.WriteString(glob.KeySymbolColon)
	builder.WriteByte('\n')
	proofStrSlice := make([]string, len(stmt.Proofs))
	for i, proof := range stmt.Proofs {
		proofStrSlice[i] = glob.SplitLinesAndAdd4NIndents(proof.String(), 1)
	}
	builder.WriteString(strings.Join(proofStrSlice, "\n"))
	return builder.String()
}

func (stmt *ProveOverFiniteSetStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordProveOverFiniteSet)
	builder.WriteString(glob.KeySymbolColon)
	builder.WriteByte('\n')
	builder.WriteString(glob.SplitLinesAndAdd4NIndents(stmt.Fact.String(), 1))
	builder.WriteByte('\n')
	builder.WriteString(glob.SplitLinesAndAdd4NIndents(stmt.Fact.String(), 1))
	builder.WriteByte('\n')
	builder.WriteString(glob.SplitLinesAndAdd4NIndents(glob.KeywordProve, 1))
	builder.WriteString(glob.KeySymbolColon)
	builder.WriteByte('\n')
	proofStrSlice := make([]string, len(stmt.Proofs))
	for i, proof := range stmt.Proofs {
		proofStrSlice[i] = glob.SplitLinesAndAdd4NIndents(proof.String(), 2)
	}
	builder.WriteString(strings.Join(proofStrSlice, "\n"))
	return builder.String()
}

func (stmt *HaveSetStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordHave)
	builder.WriteString(" ")
	builder.WriteString(stmt.Fact.String())
	return builder.String()
}

func (stmt *HaveSetFnStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordHave)
	builder.WriteString(" ")
	builder.WriteString(stmt.DefHeader.StringWithoutColonAtEnd())
	builder.WriteString(" ")
	builder.WriteString(glob.KeySymbolColonEqual)
	builder.WriteString(" ")
	builder.WriteString(stmt.Param)
	builder.WriteString(" ")
	builder.WriteString(stmt.ParentSet.String())
	builder.WriteString(glob.KeySymbolColon)
	builder.WriteByte('\n')
	proofStrSlice := make([]string, len(stmt.Proofs))
	for i, proof := range stmt.Proofs {
		proofStrSlice[i] = glob.SplitLinesAndAdd4NIndents(proof.String(), 1)
	}
	builder.WriteString(strings.Join(proofStrSlice, "\n"))
	return builder.String()
}

func (stmt *HaveSetDefinedByReplacementStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordHave)
	builder.WriteString(" ")
	builder.WriteString(stmt.Name)
	builder.WriteString(" ")
	builder.WriteString(NewFcFn(FcAtom(glob.KeywordSetDefinedByReplacement), []Fc{stmt.DomSet, stmt.RangeSet, stmt.PropName}).String())
	return builder.String()
}
