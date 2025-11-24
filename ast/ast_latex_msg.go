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

func (s *DefLetStmt) ToLatexString() string {
	var builder strings.Builder

	builder.WriteString("\\begin{definition}[Object(s)]\n")
	builder.WriteString(strFcSetPairsLatexString(s.Objs, s.ObjSets))
	builder.WriteString(".")

	if len(s.Facts) > 0 {
		builder.WriteString(" Assume object(s) satisfy:")
		factStrSlice := make([]string, len(s.Facts))
		for i := range len(s.Facts) {
			factStrSlice[i] = s.Facts[i].ToLatexString()
		}
		if ShouldInSingleLineAsLatexString(factStrSlice) {
			builder.WriteString(" ")
			builder.WriteString(strings.Join(factStrSlice, ", "))
		} else {
			builder.WriteString("\n\n")
			builder.WriteString(strings.Join(factStrSlice, "\n\n"))
		}
	}

	builder.WriteString(".")
	builder.WriteString("\n\\end{definition}")

	return builder.String()
}

func (c *DefPropStmt) ToLatexString() string {
	var builder strings.Builder

	builder.WriteString("\\begin{definition}[Proposition]\n")
	builder.WriteString(prop_fn_bodyToLatexString(c.DefHeader, c.DomFacts, c.IffFacts, false))
	builder.WriteString("\n\\end{definition}")
	return builder.String()
}

func (l *DefFnStmt) ToLatexString() string {
	var builder strings.Builder
	builder.WriteString("\\begin{definition}[Function]\n")
	builder.WriteString(l.Name)
	builder.WriteString(" is defined for ")
	builder.WriteString(strFcSetPairsLatexString(l.FnTemplate.Params, l.FnTemplate.ParamSets))
	builder.WriteString(".")

	if len(l.FnTemplate.DomFacts) > 0 {
		builder.WriteString(" Its domain is:")

		domFactStrSlice := l.FnTemplate.DomFacts.factStmtSliceToLatexStringSlice()

		if ShouldInSingleLineAsLatexString(domFactStrSlice) {
			builder.WriteString(" ")
			builder.WriteString(strings.Join(domFactStrSlice, ", "))
			builder.WriteString(".")
		} else {
			builder.WriteString("\n\n")
			builder.WriteString(strings.Join(domFactStrSlice, "\n\n"))
			builder.WriteString("\n\n")
		}
	}

	builder.WriteString(" Its return value is $\\in$ ")
	builder.WriteString(l.FnTemplate.RetSet.ToLatexString())
	builder.WriteString(".")

	if len(l.FnTemplate.ThenFacts) > 0 {
		builder.WriteString(" When its parameters satisfies the above condition, it has the following properties:")
		thenFactStrSlice := l.FnTemplate.ThenFacts.factStmtSliceToLatexStringSlice()
		if ShouldInSingleLineAsLatexString(thenFactStrSlice) {
			builder.WriteString(" ")
			builder.WriteString(strings.Join(thenFactStrSlice, ", "))
		} else {
			builder.WriteString("\n\n")
			builder.WriteString(strings.Join(thenFactStrSlice, "\n\n"))
		}
	}

	builder.WriteString("\n\\end{definition}")
	return builder.String()
}

func (l *UniFactStmt) ToLatexString() string {
	var builder strings.Builder
	builder.WriteString("$\\forall$ ")
	builder.WriteString(strFcSetPairsLatexString(l.Params, l.ParamSets))

	if len(l.DomFacts) > 0 {
		builder.WriteString(", ")
		domFactStrSlice := make([]string, len(l.DomFacts))
		for i := range len(l.DomFacts) {
			domFactStrSlice[i] = l.DomFacts[i].ToLatexString()
		}

		if ShouldInSingleLineAsLatexString(domFactStrSlice) {
			builder.WriteString(" ")
			builder.WriteString(strings.Join(domFactStrSlice, ", "))
			builder.WriteString(" ")
		} else {
			builder.WriteString("\n\n")
			builder.WriteString(strings.Join(domFactStrSlice, "\n\n"))
			builder.WriteString("\n\n")
		}
	} else {
		builder.WriteString(" ")
	}

	builder.WriteString("$\\Rightarrow$")
	thenFactStrSlice := make([]string, len(l.ThenFacts))
	for i := range len(l.ThenFacts) {
		thenFactStrSlice[i] = l.ThenFacts[i].ToLatexString()
	}

	if ShouldInSingleLineAsLatexString(thenFactStrSlice) {
		builder.WriteString(" ")
		builder.WriteString(strings.Join(thenFactStrSlice, ", "))
		builder.WriteString(" $\\rule{0.5ex}{0.5ex}$")
	} else {
		builder.WriteString("\n\n")
		builder.WriteString(strings.Join(thenFactStrSlice, "\n\n"))
		builder.WriteString("\n\n$\\rule{0.5ex}{0.5ex}$")
	}

	return builder.String()
}

func (p *SpecFactStmt) ToLatexString() string {
	if p.IsExist_St_Fact() {
		return exist_st_FactString(p)
	} else {
		return pureSpecFactLatexString(p)
	}
}

func pureSpecFactLatexString(stmt *SpecFactStmt) string {
	var builder strings.Builder

	if glob.IsKeySymbol(string(stmt.PropName)) {
		builder.WriteString(keySymbolRelaFactWithoutNotLatexString(stmt))
		if stmt.TypeEnum == FalsePure {
			builder.WriteString(" is false")
		}
		return builder.String()
	} else if _, ok := relaPropSet[string(stmt.PropName)]; ok {
		builder.WriteString(keywordRelaFactWithoutNotLatexString(stmt))
		if stmt.TypeEnum == FalsePure {
			builder.WriteString(" is false")
		}
		return builder.String()
	} else {
		curStr := strings.TrimPrefix(stmt.String(), "not ")
		curStr = strings.TrimPrefix(curStr, "$")
		curStr = fmt.Sprintf("$%s$", curStr)
		builder.WriteString(curStr)

		if stmt.TypeEnum == FalsePure {
			builder.WriteString(" is false")
		}
		return builder.String()
	}
}

func keySymbolRelaFactWithoutNotLatexString(stmt *SpecFactStmt) string {
	var builder strings.Builder

	builder.WriteString(stmt.Params[0].ToLatexString())
	builder.WriteString(" ")

	// 这里根据不同的我str的写法输出不同的latex的写法
	switch stmt.PropName {
	case glob.KeySymbolEqual:
		builder.WriteString("=")
	case glob.KeySymbolLess:
		builder.WriteString("$\\leq$")
	case glob.KeySymbolGreater:
		builder.WriteString("$\\geq$")
	case glob.KeySymbolNotEqual:
		builder.WriteString("\\neq")
	case glob.KeywordIn:
		builder.WriteString("$\\in$")
	case glob.KeySymbolLargerEqual:
		builder.WriteString("$\\geq$")
	case glob.KeySymbolLessEqual:
		builder.WriteString("$\\leq$")
	default:
		builder.WriteString(stmt.PropName.String())
	}

	builder.WriteString(" ")
	builder.WriteString(stmt.Params[1].ToLatexString())

	return builder.String()
}

func keywordRelaFactWithoutNotLatexString(stmt *SpecFactStmt) string {
	var builder strings.Builder

	builder.WriteString(stmt.Params[0].ToLatexString())
	builder.WriteString(" ")

	switch stmt.PropName {
	case glob.KeywordIn:
		builder.WriteString("$\\in$")
	default:
		builder.WriteString(stmt.PropName.String())
	}

	builder.WriteString(" ")
	builder.WriteString(stmt.Params[1].ToLatexString())

	return builder.String()
}

func prop_fn_bodyToLatexString(defHeader *DefHeader, domFacts FactStmtSlice, iffFacts FactStmtSlice, isExistProp bool) string {
	var builder strings.Builder

	builder.WriteString(defHeader.NameWithParamsLatexString())
	builder.WriteString(" is defined for ")
	builder.WriteString(strFcSetPairsLatexString(defHeader.Params, defHeader.ParamSets))
	builder.WriteString(".")

	// 处理条件部分（When）
	if len(domFacts) > 0 {
		builder.WriteString(" Its domain is:")
		domFactStrSlice := make([]string, len(domFacts))
		for i := range len(domFacts) {
			domFactStrSlice[i] = domFacts[i].ToLatexString()
		}

		if ShouldInSingleLineAsLatexString(domFactStrSlice) {
			builder.WriteString(" ")
			builder.WriteString(strings.Join(domFactStrSlice, ", "))
			builder.WriteString(".")
			builder.WriteString(" ")
		} else {
			builder.WriteString("\n\n")
			for i := range len(domFacts) {
				domFactStrSlice[i] = glob.SplitLinesAndAdd4NIndents(domFactStrSlice[i], 1)
			}
			builder.WriteString(fmt.Sprintf("%s.", strings.Join(domFactStrSlice, "\n\n")))
			builder.WriteString("\n\n")
		}

	}

	// 处理等价条件部分（Iff）
	builder.WriteString("When parameters satisfy the above properties, we say ")
	builder.WriteString(defHeader.NameWithParamsLatexString())
	if isExistProp {
		builder.WriteString(" is true if and only if there exist ")
		builder.WriteString(strFcSetPairsLatexString(defHeader.Params, defHeader.ParamSets))
		builder.WriteString(" s.t.")
	} else {
		builder.WriteString(" is true if and only if")
	}

	iffFactStrSlice := make([]string, len(iffFacts))
	for i := range len(iffFacts) {
		iffFactStrSlice[i] = iffFacts[i].ToLatexString()
	}

	if ShouldInSingleLineAsLatexString(iffFactStrSlice) {
		builder.WriteString(" ")
		builder.WriteString(fmt.Sprintf("%s.", strings.Join(iffFactStrSlice, ", ")))
		builder.WriteString(" ")
	} else {
		builder.WriteString("\n\n")
		for i := range len(iffFacts) {
			iffFactStrSlice[i] = glob.SplitLinesAndAdd4NIndents(iffFactStrSlice[i], 1)
		}
		builder.WriteString(fmt.Sprintf("%s.", strings.Join(iffFactStrSlice, "\n\n")))
	}

	return builder.String()
}

func claimProveBodyToLatexString(toCheck FactStmt, proofs StmtSlice, isProve bool) string {
	var builder strings.Builder

	builder.WriteString("\\begin{claim}\n")
	builder.WriteString(toCheck.ToLatexString())
	builder.WriteString(".\n")

	if len(proofs) > 0 {
		if isProve {
			builder.WriteString("\\begin{proof}[proof]\n")
		} else {
			builder.WriteString("\\begin{proof}[proof by contradiction]\n")
		}
		proofStrSlice := make([]string, len(proofs))
		for i := range len(proofs) {
			proofStrSlice[i] = proofs[i].ToLatexString()
		}
		if ShouldInSingleLineAsLatexString(proofStrSlice) {
			builder.WriteString(strings.Join(proofStrSlice, ", "))
			builder.WriteString(".")
		} else {
			builder.WriteString(strings.Join(proofStrSlice, "\n\n"))
		}
		builder.WriteString("\n\\end{proof}")
	}

	builder.WriteString("\n\\end{claim}")

	return builder.String()
}

func (f *ClaimProveStmt) ToLatexString() string {
	return claimProveBodyToLatexString(f.ToCheckFact, f.Proofs, true)
}

func (f *KnowFactStmt) ToLatexString() string {
	var builder strings.Builder

	builder.WriteString("\\begin{assumption}\n\n")

	if len(f.Facts) == 1 {
		builder.WriteString("The following fact is assumed to be true:\n\n")
	} else {
		builder.WriteString("The following fact(s) are assumed to be true:\n\n")
	}

	if len(f.Facts) > 1 {
		builder.WriteString("\\begin{enumerate}\n\n")
	}

	for _, fact := range f.Facts {
		builder.WriteString("\\item ")
		builder.WriteString(fact.ToLatexString())
		builder.WriteString("\n")
	}

	if len(f.Facts) > 1 {
		builder.WriteString("\n\\end{enumerate}\n")
	}
	builder.WriteString("\n\\end{assumption}")
	return builder.String()
}

func (s *DefExistPropStmt) ToLatexString() string {
	var builder strings.Builder

	builder.WriteString("\\begin{definition}[Existential Proposition]\n")
	builder.WriteString(prop_fn_bodyToLatexString(s.DefBody.DefHeader, s.DefBody.DomFacts, s.DefBody.IffFacts, true))
	builder.WriteString("\n\\end{definition}")
	return builder.String()
}

func (s *HaveObjStStmt) ToLatexString() string {
	var builder strings.Builder

	builder.WriteString("\\begin{definition}[Object(s) Exists By Verified Existential Fact]\n")

	builder.WriteString(" we have ")
	builder.WriteString(fcParamsLatexString(s.Fact.Params))
	builder.WriteString(fmt.Sprintf(" which makes existential fact %s true", propNameParamsLatexString(s.Fact.PropName, s.Fact.Params)))

	builder.WriteString("\n\\end{definition}")
	return builder.String()
}

func (s *ProveInEachCaseStmt) ToLatexString() string {
	var builder strings.Builder
	builder.WriteString("\\begin{proveCaseByCase}\n")
	builder.WriteString("Since ")
	builder.WriteString(s.OrFact.ToLatexString())
	builder.WriteString(" is true.")
	builder.WriteString(" we prove ")
	builder.WriteString(strings.Join(s.ThenFacts.factStmtSliceToLatexStringSlice(), ", "))
	builder.WriteString(glob.KeySymbolColon)
	builder.WriteString("case by case:\n")
	for i := range s.Proofs {
		builder.WriteString(fmt.Sprintf("Case %d: %s\n", i+1, s.OrFact.Facts[i]))
		stmtSlice := make([]string, len(s.Proofs[i]))
		for j, proof := range s.Proofs[i] {
			stmtSlice[j] = proof.ToLatexString()
		}
		builder.WriteString(strings.Join(stmtSlice, ", "))
		builder.WriteString("\n")
	}

	builder.WriteString("\n\\end{proveCaseByCase}")
	return builder.String()
}

func (s *ProveCaseByCaseStmt) ToLatexString() string {
	return s.String()
}

func (s *KnowPropStmt) ToLatexString() string {
	var builder strings.Builder
	builder.WriteString(s.Prop.ToLatexString())
	builder.WriteString("\\begin{assumption}\n")
	builder.WriteString(s.Prop.ToForallWhenPropIsTrue_Then_ThenSectionOfPropIsTrue().ToLatexString())
	builder.WriteString("\n\\end{assumption}")
	return builder.String()
}

func (s *OrStmt) ToLatexString() string {
	factStrSlice := make([]string, len(s.Facts))
	for i := range len(s.Facts) {
		factStrSlice[i] = s.Facts[i].ToLatexString()
	}
	return strings.Join(factStrSlice, " or ")
}

func (s *ImportDirStmt) ToLatexString() string {
	var builder strings.Builder
	builder.WriteString("\\begin{import}\n")
	builder.WriteString("Import directory ")
	builder.WriteString(s.Path)
	builder.WriteString(" as ")
	builder.WriteString(s.AsPkgName)
	builder.WriteString("\n\\end{import}")
	return builder.String()
}

func (s *ImportFileStmt) ToLatexString() string {
	var builder strings.Builder
	builder.WriteString("\\begin{import}\n")
	builder.WriteString("Import file ")
	builder.WriteString(s.Path)
	builder.WriteString("\n\\end{import}")
	return builder.String()
}

func (s *ProveStmt) ToLatexString() string {
	var builder strings.Builder
	builder.WriteString("\\begin{example}\n\n")
	stmtSlice := make([]string, len(s.Proof))
	for i := range s.Proof {
		stmtSlice[i] = s.Proof[i].ToLatexString()
	}

	if ShouldInSingleLineAsLatexString(stmtSlice) {
		builder.WriteString(strings.Join(stmtSlice, ", "))
	} else {
		builder.WriteString(strings.Join(stmtSlice, "\n\n"))
	}

	builder.WriteString("\n\n\\end{example}")
	return builder.String()
}

func (s *UniFactWithIffStmt) ToLatexString() string {
	var builder strings.Builder
	builder.WriteString("$\\forall$ ")

	builder.WriteString(strings.Join(paramInParamSetInFactLatexStringSlice(s.UniFact.Params, s.UniFact.ParamSets), ", "))

	if len(s.UniFact.DomFacts) > 0 {

		domFactStrSlice := s.UniFact.DomFacts.factStmtSliceToLatexStringSlice()

		if ShouldInSingleLineAsLatexString(domFactStrSlice) {
			builder.WriteString(",  ")
			builder.WriteString(strings.Join(domFactStrSlice, ", "))
			builder.WriteString(" ")
		} else {
			builder.WriteString(", \n\n")
			builder.WriteString(strings.Join(domFactStrSlice, "\n\n"))
			builder.WriteString("\n\n")
		}
	}

	if len(s.UniFact.ThenFacts) > 0 {
		thenFactStrSlice := s.UniFact.ThenFacts.factStmtSliceToLatexStringSlice()
		if ShouldInSingleLineAsLatexString(thenFactStrSlice) {
			builder.WriteString("$\\Rightarrow$ ")
			builder.WriteString(strings.Join(thenFactStrSlice, ", "))
			builder.WriteString(" ")
		} else {
			builder.WriteString("$\\Rightarrow$\n\n")
			builder.WriteString(strings.Join(thenFactStrSlice, "\n\n"))
			builder.WriteString("\n\n")
		}
	}

	if len(s.IffFacts) > 0 {
		builder.WriteString("if and only if ")
		iffFactStrSlice := s.IffFacts.factStmtSliceToLatexStringSlice()
		if ShouldInSingleLineAsLatexString(iffFactStrSlice) {
			builder.WriteString(" ")
			builder.WriteString(strings.Join(iffFactStrSlice, ", "))
		} else {
			builder.WriteString("\n\n")
			builder.WriteString(strings.Join(iffFactStrSlice, "\n\n"))
		}
	}

	builder.WriteString(".")
	return builder.String()
}

func (s *ClaimProveByContradictionStmt) ToLatexString() string {
	return claimProveBodyToLatexString(s.ClaimProveStmt.ToCheckFact, s.ClaimProveStmt.Proofs, false)
}

func (s *EnumStmt) ToLatexString() string {
	var builder strings.Builder
	builder.WriteString(s.CurSet.ToLatexString())
	builder.WriteString(" = \\{")

	strSlice := make([]string, len(s.Items))
	for i := range len(s.Items) {
		strSlice[i] = s.Items[i].ToLatexString()
	}
	builder.WriteString(strings.Join(strSlice, ", "))

	builder.WriteString("\\}")
	return fmt.Sprintf("$%s$", strings.ReplaceAll(builder.String(), "$", ""))
}

func intentionalSetOrIntensionalSetToLatexString(param string, parentSet Obj, proofs SpecFactPtrSlice) string {
	var builder strings.Builder
	builder.WriteString(" = \\{")
	builder.WriteString(param)
	builder.WriteString(" $\\in$ ")
	builder.WriteString(parentSet.ToLatexString())
	builder.WriteString(" | ")
	proofStrSlice := make([]string, len(proofs))
	for i := range len(proofs) {
		proofStrSlice[i] = proofs[i].ToLatexString()
	}
	builder.WriteString(strings.Join(proofStrSlice, ", "))
	builder.WriteString("\\}")
	return fmt.Sprintf("$%s$", strings.ReplaceAll(builder.String(), "$", ""))
}

func (s *IntensionalSetStmt) ToLatexString() string {
	var builder strings.Builder
	builder.WriteString(s.CurSet.ToLatexString())

	builder.WriteString(intentionalSetOrIntensionalSetToLatexString(s.Param, s.ParentSet, s.Facts))

	return builder.String()
}

func (s *ClaimPropStmt) ToLatexString() string {
	var builder strings.Builder

	builder.WriteString(s.ToProp().ToLatexString())

	builder.WriteString("\n\n")

	builder.WriteString(claimProveBodyToLatexString(s.Prop.ToForallWhenPropIsTrue_Then_ThenSectionOfPropIsTrue(), s.Proofs, true))

	return builder.String()
}

// TODO
func (s *ClaimExistPropStmt) ToLatexString() string {
	var builder strings.Builder

	builder.WriteString(s.ExistPropWithoutDom.ToLatexString())

	builder.WriteString("\n\n")

	builder.WriteString(claimProveBodyToLatexString(s.ExistPropWithoutDom.ToForallParamsSatisfyDomFacts_Then_ExistFactIsTrue(), s.Proofs, true))

	return builder.String()
}

func (s *ProveByEnumStmt) ToLatexString() string {
	var builder strings.Builder
	builder.WriteString("\\begin{proveOverFiniteSet}\n")
	builder.WriteString("We prove that by iterating over the elements of the finite set(s): ")
	builder.WriteString(strings.Join(paramInParamSetInFactLatexStringSlice(s.Fact.Params, s.Fact.ParamSets), ", "))
	builder.WriteString(". ")
	builder.WriteString(s.Fact.ToLatexString())
	builder.WriteString("\n")

	builder.WriteString("\\begin{proof}\n")

	proofStrSlice := make([]string, len(s.Proof))
	for i := range len(s.Proof) {
		proofStrSlice[i] = s.Proof[i].ToLatexString()
	}

	if ShouldInSingleLineAsLatexString(proofStrSlice) {
		builder.WriteString(strings.Join(proofStrSlice, ", "))
	} else {
		builder.WriteString(strings.Join(proofStrSlice, "\n\n"))
	}

	builder.WriteString("\n\\end{proof}")

	builder.WriteString("\n\\end{proveOverFiniteSet}")
	return builder.String()
}

func (s *HaveObjInNonEmptySetStmt) ToLatexString() string {
	var builder strings.Builder
	builder.WriteString("\\begin{definition}[Object(s) Exists By Verified Existential Fact]\n")

	builder.WriteString("We have objects from nonempty set(s): ")
	builder.WriteString(strings.Join(paramInParamSetInFactLatexStringSlice(s.Objs, s.ObjSets), ", "))
	builder.WriteString(".\n")

	builder.WriteString("\\end{definition}")
	return builder.String()
}

func (s *HaveEnumSetStmt) ToLatexString() string {
	var builder strings.Builder
	builder.WriteString("\\begin{definition}[Set Exist By Axioms of Set Theory]")

	builder.WriteString("We have a set: ")

	builder.WriteString(s.Fact.ToLatexString())

	builder.WriteString(".\n")

	builder.WriteString("\\end{definition}")
	return builder.String()
}

func (s *HaveIntensionalSetStmt) ToLatexString() string {
	var builder strings.Builder
	builder.WriteString("\\begin{definition}[Set Exist By Axioms of Set Theory]")
	builder.WriteString("We have a set: ")
	builder.WriteString(s.Fact.ToLatexString())
	builder.WriteString(".\n")
	builder.WriteString("\\end{definition}")
	return builder.String()
}

func (s *HaveCartSetStmt) ToLatexString() string {
	var builder strings.Builder
	builder.WriteString("\\begin{definition}[Set Exist By Axioms of Set Theory]")
	builder.WriteString("We have a set: ")
	builder.WriteString(s.Name)
	builder.WriteString(" = ")
	builder.WriteString(s.CartObj.ToLatexString())
	builder.WriteString(".\n")
	builder.WriteString("\\end{definition}")
	return builder.String()
}

func (s *HaveSetFnStmt) ToLatexString() string {
	var builder strings.Builder
	builder.WriteString("\\begin{definition}[Function Exist By Axioms of Set Theory]")
	builder.WriteString(fmt.Sprintf("We have a function %s returning a set, whose domain is: ", s.DefHeader.NameWithParamsLatexString()))
	builder.WriteString(strings.Join(paramInParamSetInFactLatexStringSlice(s.DefHeader.Params, s.DefHeader.ParamSets), ", "))
	builder.WriteString(". ")
	builder.WriteString(s.DefHeader.NameWithParamsLatexString())

	builder.WriteString(intentionalSetOrIntensionalSetToLatexString(s.Param, s.ParentSet, s.Proofs))

	builder.WriteString(".")

	builder.WriteString("\n\\end{definition}")
	return builder.String()
}

func (s *HaveSetDefinedByReplacementStmt) ToLatexString() string {
	var builder strings.Builder
	builder.WriteString("\\begin{definition}[Set Exist By Axioms of Set Theory]")

	builder.WriteString("By axiom of replacement, we have a set: ")
	{
		var setBuilder strings.Builder
		setBuilder.WriteString(s.Name)
		setBuilder.WriteString(" = \\{")
		setBuilder.WriteString("y $\\in$ ")
		setBuilder.WriteString(s.DomSet.ToLatexString())
		setBuilder.WriteString(" | \\textnormal{there exists} x \\textnormal{s.t.} ")
		setBuilder.WriteString(s.PropName.String())
		setBuilder.WriteString("(x, y) \\textnormal{is true}.")
		setBuilder.WriteString("\\}")
		builder.WriteString(fmt.Sprintf("$%s$", strings.ReplaceAll(setBuilder.String(), "$", "")))
	}

	builder.WriteString("\n\\end{definition}")
	return builder.String()
}

func (s *NamedUniFactStmt) ToLatexString() string {
	var builder strings.Builder
	builder.WriteString(s.DefPropStmt.ToLatexString())
	builder.WriteString("\n\n")

	builder.WriteString(VerifiedFactsSectionToLatexString(s.DefPropStmt.IffFacts))

	return builder.String()
}

func VerifiedFactsSectionToLatexString(verifiedFacts []FactStmt) string {
	var builder strings.Builder

	builder.WriteString("\\begin{checkFacts} We check:\n")

	strSlice := make([]string, len(verifiedFacts))
	for i, fact := range verifiedFacts {
		strSlice[i] = fact.ToLatexString()
	}

	if ShouldInSingleLineAsLatexString(strSlice) {
		builder.WriteString(strings.Join(strSlice, ", "))
	} else {
		builder.WriteString("\n")
		builder.WriteString(strings.Join(strSlice, "\n\n"))
	}

	builder.WriteString("\\end{checkFacts}")

	return builder.String()
}

func (s *EqualsFactStmt) ToLatexString() string {
	var builder strings.Builder
	builder.WriteString("The following objects are equal: ")
	builder.WriteString(strings.Join(s.Params.fcSliceToLatexStringSlice(), ", "))
	builder.WriteString(".")
	return builder.String()
}

func (s *KnowExistPropStmt) ToLatexString() string {
	var builder strings.Builder
	defExistProp := NewDefExistPropStmt(s.ExistProp.DefBody, s.ExistProp.ExistParams, s.ExistProp.ExistParamSets, glob.InnerGenLine)
	builder.WriteString(defExistProp.ToLatexString())

	builder.WriteString("\n\n")
	builder.WriteString("We assume existential proposition is true for all parameters in the proposition's domain.")

	return builder.String()
}

func (s *LatexStmt) ToLatexString() string {
	return s.Comment
}

func (s *FnTemplateDefStmt) ToLatexString() string {
	var builder strings.Builder
	builder.WriteString("\\begin{definition}[Function Template]\n\n")

	if len(s.TemplateDomFacts) > 0 {
		builder.WriteString("When")
		factStrSlice := s.TemplateDomFacts.factStmtSliceToLatexStringSlice()
		if ShouldInSingleLineAsLatexString(factStrSlice) {
			builder.WriteString(" ")
			builder.WriteString(strings.Join(factStrSlice, ", "))
		} else {
			builder.WriteString("\n\n")
			builder.WriteString(strings.Join(factStrSlice, "\n\n"))
		}
		builder.WriteString("\n\n")
	}

	builder.WriteString(fmt.Sprintf("We say a function $\\in$ function template %s ", s.TemplateDefHeader.NameWithParamsLatexString()))

	builder.WriteString(fmt.Sprintf("if it satisfies (we use %s here to represent that function here):", toLatexString(string(s.TemplateDefHeader.Name))))
	builder.WriteString("\n\n")

	builder.WriteString("It has a domain which is superset of the set which contains parameters satisfying the following properties: ")
	builder.WriteString(strings.Join(paramInParamSetInFactLatexStringSlice(s.TemplateDefHeader.Params, s.TemplateDefHeader.ParamSets), ", "))

	if len(s.TemplateDomFacts) > 0 {
		builder.WriteString(" and ")
		domFactStrSlice := s.TemplateDomFacts.factStmtSliceToLatexStringSlice()
		if ShouldInSingleLineAsLatexString(domFactStrSlice) {
			builder.WriteString(" ")
			builder.WriteString(strings.Join(domFactStrSlice, ", "))
		} else {
			builder.WriteString("\n\n")
			builder.WriteString(strings.Join(domFactStrSlice, "\n\n"))
		}
		builder.WriteString(".")
	} else {
		builder.WriteString(".")
	}

	if len(s.Fn.ThenFacts) > 0 {
		builder.WriteString("\n\n")
		builder.WriteString("When its parameters satisfies the above condition, it has the following properties:")
		thenFactStrSlice := s.Fn.ThenFacts.factStmtSliceToLatexStringSlice()
		if ShouldInSingleLineAsLatexString(thenFactStrSlice) {
			builder.WriteString(" ")
			builder.WriteString(strings.Join(thenFactStrSlice, ", "))
		} else {
			builder.WriteString("\n\n")
			builder.WriteString(strings.Join(thenFactStrSlice, "\n\n"))
		}
		builder.WriteString(".")
	}

	builder.WriteString("\n\n")

	builder.WriteString("The return value is $\\in$ ")
	builder.WriteString(s.Fn.RetSet.ToLatexString())

	builder.WriteString("\n\\end{definition}")

	return builder.String()
}

func (s *ClearStmt) ToLatexString() string {
	return glob.KeywordClear
}

func (s *InlineFactsStmt) ToLatexString() string {
	var builder strings.Builder
	builder.WriteString(strings.Join(s.Facts.factStmtSliceToLatexStringSlice(), "\n\n"))
	return builder.String()
}

func (s *ProveByInductionStmt) ToLatexString() string {
	var builder strings.Builder
	builder.WriteString("\\begin{proveByMathInduction}\n")
	builder.WriteString("By mathematical induction, we have ")
	builder.WriteString(s.Fact.ToLatexString())
	builder.WriteString(" is true $\\forall$ ")
	builder.WriteString(s.Param)
	builder.WriteString(" $\\geq$ ")
	builder.WriteString(s.Start.ToLatexString())
	builder.WriteString(".")
	builder.WriteString("\n\\end{proveByMathInduction}")
	return builder.String()
}

func (s *HaveObjEqualStmt) ToLatexString() string {
	var builder strings.Builder
	builder.WriteString("\\begin{definition}[Object(s)]\n")
	strSlice := make([]string, len(s.ObjNames))
	for i := range len(s.ObjNames) {
		strSlice[i] = fmt.Sprintf("%s %s %s", s.ObjNames[i], glob.KeySymbolEqual, s.ObjEqualTos[i].ToLatexString())
	}
	builder.WriteString(strings.Join(strSlice, ", "))
	builder.WriteString("\\end{definition}")
	return builder.String()
}

func (s *HaveFnEqualStmt) ToLatexString() string {
	var builder strings.Builder
	builder.WriteString("\\begin{definition}[Function]\n")
	builder.WriteString(s.DefHeader.NameWithParamsLatexString())
	builder.WriteString(" ")
	builder.WriteString(glob.KeySymbolEqual)
	builder.WriteString(" ")
	builder.WriteString(s.EqualTo.ToLatexString())
	builder.WriteString("\\end{definition}")
	return builder.String()
}

func (s *HaveFnLiftStmt) ToLatexString() string {
	var builder strings.Builder
	builder.WriteString("\\begin{definition}[Function]\n")
	builder.WriteString(s.FnName)
	builder.WriteString(" ")
	builder.WriteString(glob.KeySymbolEqual)
	builder.WriteString(" ")
	builder.WriteString(glob.KeywordLift)
	builder.WriteString("(")
	builder.WriteString(s.Opt.ToLatexString())
	builder.WriteString(", ")
	builder.WriteString(" ")
	builder.WriteString(glob.KeySymbolLeftBrace)
	builder.WriteString(strings.Join(s.DomainOfEachParamOfGivenFn.fcSliceToLatexStringSlice(), ", "))
	builder.WriteString(glob.KeySymbolRightBrace)
	builder.WriteString(".")
	builder.WriteString("\n\\end{definition}")
	return builder.String()
}

func (s *HaveFnStmt) ToLatexString() string {
	return s.String()
}

func (s *HaveFnCaseByCaseStmt) ToLatexString() string {
	return s.String()
}

func (s *MarkdownStmt) ToLatexString() string {
	return s.Markdown
}

// func (s *ProveInRange2tmt) ToLatexString() string {
// 	return "TODO"
// }

func (s *ClaimIffStmt) ToLatexString() string {
	return s.String()
}

func (s *ProveInRangeSetStmt) ToLatexString() string {
	return s.String()
}

func (s *ProveInRangeStmt) ToLatexString() string {
	return s.String()
}

func (s *ProveIsTransitivePropStmt) ToLatexString() string {
	return s.String()
}

func (s *ProveIsCommutativePropStmt) ToLatexString() string {
	return s.String()
}

func (s *AlgoIfStmt) ToLatexString() string {
	return s.String()
}

func (s *AlgoReturnStmt) ToLatexString() string {
	return s.String()
}

func (s *DefAlgoStmt) ToLatexString() string {
	return s.String()
}

func (s *EvalStmt) ToLatexString() string {
	return fmt.Sprintf("%s(%s)", glob.KeywordEval, s.FcsToEval.ToLatexString())
}

func (s *DefProveAlgoStmt) ToLatexString() string {
	return s.String()
}

func (s *ByStmt) ToLatexString() string {
	return s.String()
}

func (s *ProveAlgoReturnStmt) ToLatexString() string {
	return s.String()
}

func (s *PrintStmt) ToLatexString() string {
	return s.String()
}

func (s *HelpStmt) ToLatexString() string {
	return s.String()
}

func (s *HaveFnEqualCaseByCaseStmt) ToLatexString() string {
	return s.String()
}
