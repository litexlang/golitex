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

		builder.WriteString(fcSliceString(stmt.Params))
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

func StrFcSetPairs(objs []string, objSets []Fc) string {
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

	builder.WriteString(fcSliceString(existParams))
	builder.WriteString(" ")
	builder.WriteString(glob.KeywordSt)
	builder.WriteString(" ")
	builder.WriteString(NewSpecFactStmt(TruePure, stmt.PropName, factParams, glob.InnerGenLine).String())

	return builder.String()
}

func (stmt *DefObjStmt) String() string {
	var builder strings.Builder

	builder.WriteString(glob.KeywordLet)
	builder.WriteString(" ")
	builder.WriteString(StrFcSetPairs(stmt.Objs, stmt.ObjSets))

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
	builder.WriteString(StrFcSetPairs(stmt.Objs, stmt.ObjSets))

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
		// builder.WriteString(glob.SplitLinesAndAdd4NIndents(glob.KeywordIff, 1))
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(glob.KeySymbolEquivalent, 1))
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

func fnDefStmtStringGivenKw(kw string, f *FnTStruct, name string) string {
	var builder strings.Builder
	builder.WriteString(kw)
	builder.WriteString(" ")
	builder.WriteString(name)
	builder.WriteString("(")
	builder.WriteString(StrFcSetPairs(f.Params, f.ParamSets))
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
		builder.WriteString(glob.SplitLinesAndAdd4NIndents("<=>:", 1))
		builder.WriteString("\n")

		iffFactStrSlice := make([]string, len(s.DefBody.IffFacts))
		for i := range len(s.DefBody.IffFacts) {
			iffFactStrSlice[i] = glob.SplitLinesAndAdd4NIndents(s.DefBody.IffFacts[i].String(), 2)
		}
		builder.WriteString(strings.Join(iffFactStrSlice, "\n"))
	}

	return builder.String()
}

func (s *DefExistPropStmt) String() string {
	return s.ToString(glob.KeywordExistProp)
}

func (l *UniFactStmt) String() string {
	var builder strings.Builder

	builder.WriteString(glob.KeywordForall)
	builder.WriteString(" ")

	builder.WriteString(StrFcSetPairs(l.Params, l.ParamSets))

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

	builder.WriteString(StrFcSetPairs(head.Params, head.ParamSets))

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

	if IsFcAtomAndEqualToStr(f.FnHead, glob.KeySymbolDot) {
		return fmt.Sprintf("%s.%s", f.Params[0], f.Params[1])
	}

	if IsFcAtomAndEqualToStr(f.FnHead, glob.TupleFcFnHead) {
		paramStrSlice := make([]string, len(f.Params))
		for i := range len(f.Params) {
			paramStrSlice[i] = f.Params[i].String()
		}
		return fmt.Sprintf("(%s)", strings.Join(paramStrSlice, ", "))
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

func (stmt *KnowPropStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordKnow)
	builder.WriteString(" ")
	builder.WriteString(stmt.Prop.String())
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
	return fnDefStmtStringGivenKw(glob.KeywordFn, stmt.FnTemplate, stmt.Name)
}

func (stmt *EnumStmt) String() string {
	var builder strings.Builder
	builder.WriteString(stmt.CurSet.String())
	builder.WriteString(" ")
	// builder.WriteString(glob.KeySymbolColonEqual)
	builder.WriteString(glob.KeySymbolEqual)
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
	builder.WriteString(glob.KeySymbolAt)
	builder.WriteString(stmt.DefHeader.String())
	builder.WriteString(glob.KeySymbolColon)
	builder.WriteByte('\n')

	var iffFactStrSlice []string
	for _, iffFact := range stmt.IffFacts {
		iffFactStrSlice = append(iffFactStrSlice, glob.SplitLinesAndAdd4NIndents(iffFact.String(), 2))
	}
	builder.WriteString(strings.Join(iffFactStrSlice, "\n"))
	builder.WriteByte('\n')

	var thenFactStrSlice []string
	builder.WriteString(glob.SplitLinesAndAdd4NIndents(glob.KeySymbolRightArrow, 1))
	builder.WriteString(glob.KeySymbolColon)
	builder.WriteByte('\n')
	for _, thenFact := range stmt.ThenFacts {
		thenFactStrSlice = append(thenFactStrSlice, glob.SplitLinesAndAdd4NIndents(thenFact.String(), 2))
	}
	builder.WriteString(strings.Join(thenFactStrSlice, "\n"))
	return builder.String()
}

func (stmt *ClaimPropStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordClaim)
	builder.WriteString(glob.KeySymbolColon)
	builder.WriteString("\n")
	builder.WriteString(glob.SplitLinesAndAdd4NIndents(stmt.Prop.ToNamedUniFactString(), 1))
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

// func (stmt *ProveByMathInductionStmt) String() string {
// 	var builder strings.Builder
// 	builder.WriteString(glob.KeywordProveByMathInduction)
// 	builder.WriteString("(")
// 	builder.WriteString(stmt.Fact.String())
// 	builder.WriteString(", ")
// 	builder.WriteString(fmt.Sprintf("%d", stmt.ParamIndex))
// 	builder.WriteString(", ")
// 	builder.WriteString(fmt.Sprintf("%d", stmt.Start))
// 	builder.WriteString(")")
// 	return builder.String()
// }

func (stmt *IntensionalSetStmt) String() string {
	var builder strings.Builder
	builder.WriteString(stmt.CurSet.String())
	builder.WriteString(" ")
	// builder.WriteString(glob.KeySymbolColonEqual)
	builder.WriteString(glob.KeySymbolEqual)
	builder.WriteString(" ")
	builder.WriteString(glob.KeySymbolLeftCurly)
	builder.WriteString(stmt.Param)
	builder.WriteString(" ")
	builder.WriteString(stmt.ParentSet.String())
	builder.WriteString(" ")
	builder.WriteString(glob.KeySymbolColon)
	proofStrSlice := make([]string, len(stmt.Facts))
	for i := range len(stmt.Facts) {
		proofStrSlice[i] = stmt.Facts[i].InlineString()
	}
	builder.WriteString(strings.Join(proofStrSlice, ", "))
	builder.WriteString(glob.KeySymbolRightCurly)
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
	// builder.WriteString(glob.KeySymbolColonEqual)
	builder.WriteString(glob.KeySymbolEqual)
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

func (stmt *NamedUniFactStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeySymbolAt)
	builder.WriteString(" ")
	builder.WriteString(stmt.DefPropStmt.String())
	return builder.String()
}

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

func (stmt *LatexStmt) String() string {
	return stmt.Comment
}

func (stmt *FnTemplateDefStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordFnTemplate)
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
	builder.WriteString(stmt.DefHeader.StringWithoutColonAtEnd())
	builder.WriteString(" ")
	builder.WriteString(stmt.RetSet.String())
	builder.WriteString(" ")
	builder.WriteString(glob.KeySymbolEqual)
	builder.WriteString(" ")
	builder.WriteString(stmt.EqualTo.String())

	return builder.String()
}

func (stmt *HaveFnLiftStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordHave)
	builder.WriteString(" ")
	builder.WriteString(stmt.FnName)
	builder.WriteString(" ")
	builder.WriteString(glob.KeySymbolEqual)
	builder.WriteString(" ")
	builder.WriteString(glob.KeywordLift)
	builder.WriteString("(")
	builder.WriteString(stmt.Opt.String())
	builder.WriteString(", ")
	strSlice := []string{}
	for _, param := range stmt.DomainOfEachParamOfGivenFn {
		strSlice = append(strSlice, param.String())
	}
	builder.WriteString(strings.Join(strSlice, ", "))
	builder.WriteString(")")
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

func (fc FcSlice) String() string {
	output := make([]string, len(fc))
	for i, param := range fc {
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

func (stmt *MarkdownStmt) String() string {
	return stmt.Markdown
}

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

func (stmt *ProveInRangeStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordProveInRange)
	builder.WriteString("(")
	builder.WriteString(fmt.Sprintf("%d", stmt.Start))
	builder.WriteString(", ")
	builder.WriteString(fmt.Sprintf("%d", stmt.End))
	builder.WriteString(", ")
	builder.WriteString(stmt.Param)
	builder.WriteString(" ")
	builder.WriteString(stmt.IntensionalSet.String())
	builder.WriteString(")")
	builder.WriteString(glob.KeySymbolColon)
	builder.WriteByte('\n')
	for _, fact := range stmt.ThenFacts {
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(fact.String(), 1))
		builder.WriteByte('\n')
	}
	if len(stmt.Proofs) > 0 {
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(glob.KeywordProve, 1))
		builder.WriteString(glob.KeySymbolColon)
		builder.WriteByte('\n')
		for _, proof := range stmt.Proofs {
			builder.WriteString(glob.SplitLinesAndAdd4NIndents(proof.String(), 2))
			builder.WriteByte('\n')
		}
	}
	return builder.String()
}

func (stmt *ProveIsTransitivePropStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordProveIsTransitiveProp)
	builder.WriteString("(")
	builder.WriteString(stmt.Prop.String())
	builder.WriteString(")")
	builder.WriteString(glob.KeySymbolColon)
	builder.WriteByte('\n')
	for _, proof := range stmt.Proofs {
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(proof.String(), 1))
		builder.WriteByte('\n')
	}
	return builder.String()
}
