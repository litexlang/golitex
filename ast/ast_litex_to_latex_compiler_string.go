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

func ShouldInSingleLineAsLatexString(strSlice []string) bool {
	totalLength := 0
	for _, s := range strSlice {
		totalLength += len(s)
	}
	return totalLength < 80
}

func toLatexString(s string) string {
	return fmt.Sprintf("$%s$", strings.ReplaceAll(s, "_", "\\_"))
}

func strFcSetPairsLatexString(objs []string, objSets []Fc) string {
	pairStrSlice := make([]string, len(objs))
	for i := range len(objs) {
		pairStrSlice[i] = fmt.Sprintf("%s $\\in$ %s", toLatexString(objs[i]), objSets[i].ToLatexString())
	}
	return strings.Join(pairStrSlice, ", ")
}

func (s *DefObjStmt) ToLatexString() string {
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

func (head DefHeader) ToLatexString() string {
	return fmt.Sprintf("$%s$", strings.ReplaceAll(head.String(), "_", "\\_"))
}

func (head DefHeader) NameWithParamsLatexString() string {
	var builder strings.Builder
	builder.WriteString(head.Name)
	builder.WriteString("(")
	builder.WriteString(strings.Join(head.Params, ", "))
	builder.WriteString(")")
	return fmt.Sprintf("$%s$", strings.ReplaceAll(builder.String(), "_", "\\_"))
}

func bodyToLatexString(defHeader *DefHeader, domFacts FactStmtSlice, iffFacts FactStmtSlice, isExistProp bool) string {
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

func (c *DefPropStmt) ToLatexString() string {
	var builder strings.Builder

	// 定义命题部分（自然语言风格）
	builder.WriteString("\\begin{definition}[Proposition]\n")
	builder.WriteString(bodyToLatexString(&c.DefHeader, c.DomFacts, c.IffFacts, false))
	builder.WriteString("\n\\end{definition}")
	return builder.String()
}

func (l *DefFnStmt) ToLatexString() string {
	var builder strings.Builder

	builder.WriteString("\\begin{definition}[Function]\n")
	builder.WriteString(l.FnTemplateStmt.DefHeader.NameWithParamsLatexString())
	builder.WriteString(" is defined for ")
	builder.WriteString(strFcSetPairsLatexString(l.FnTemplateStmt.Params, l.FnTemplateStmt.ParamSets))
	builder.WriteString(".")

	if len(l.FnTemplateStmt.DomFacts) > 0 {
		builder.WriteString(" Its domain is:")

		domFactStrSlice := make([]string, len(l.FnTemplateStmt.DomFacts))
		for i := range len(l.FnTemplateStmt.DomFacts) {
			domFactStrSlice[i] = l.FnTemplateStmt.DomFacts[i].ToLatexString()
		}

		if ShouldInSingleLineAsLatexString(domFactStrSlice) {
			builder.WriteString(" ")
			builder.WriteString(fmt.Sprintf("%s.", strings.Join(domFactStrSlice, ", ")))
			builder.WriteString(" ")
		} else {
			builder.WriteString("\n\n")
			for i := range len(l.FnTemplateStmt.DomFacts) {
				domFactStrSlice[i] = glob.SplitLinesAndAdd4NIndents(domFactStrSlice[i], 1)
			}
			builder.WriteString(fmt.Sprintf("%s.", strings.Join(domFactStrSlice, "\n\n")))
			builder.WriteString("\n\n")
		}
	}

	if len(l.FnTemplateStmt.ThenFacts) > 0 {
		builder.WriteString(fmt.Sprintf("We suppose %s satisfies:", toLatexString(l.FnTemplateStmt.DefHeader.Name)))

		thenFactStrSlice := make([]string, len(l.FnTemplateStmt.ThenFacts))
		for i := range len(l.FnTemplateStmt.ThenFacts) {
			thenFactStrSlice[i] = l.FnTemplateStmt.ThenFacts[i].ToLatexString()
		}

		if ShouldInSingleLineAsLatexString(thenFactStrSlice) {
			builder.WriteString(" ")
			builder.WriteString(fmt.Sprintf("%s.", strings.Join(thenFactStrSlice, ", ")))
			builder.WriteString(" ")
		} else {
			builder.WriteString("\n\n")
			for i := range len(l.FnTemplateStmt.ThenFacts) {
				thenFactStrSlice[i] = glob.SplitLinesAndAdd4NIndents(thenFactStrSlice[i], 1)
			}
			builder.WriteString(fmt.Sprintf("%s.", strings.Join(thenFactStrSlice, "\n\n")))
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
		builder.WriteString(", when")
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

	builder.WriteString("then:")
	thenFactStrSlice := make([]string, len(l.ThenFacts))
	for i := range len(l.ThenFacts) {
		thenFactStrSlice[i] = l.ThenFacts[i].ToLatexString()
	}

	if ShouldInSingleLineAsLatexString(thenFactStrSlice) {
		builder.WriteString(" ")
		builder.WriteString(strings.Join(thenFactStrSlice, ", "))
	} else {
		builder.WriteString("\n\n")
		builder.WriteString(strings.Join(thenFactStrSlice, "\n\n"))
	}

	builder.WriteString(".")

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
	case glob.KeySymbolEqualEqual:
		builder.WriteString("==")
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

func claimProveBodyToLatexString(toCheck FactStmt, proofs StmtSlice, isProve bool) string {
	var builder strings.Builder

	builder.WriteString("\\begin{claim}\n")
	builder.WriteString(toCheck.ToLatexString())
	builder.WriteString(".")

	if len(proofs) > 0 {
		builder.WriteString("\\begin{proof}\n")
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

func (s FactStmtSlice) factStmtSliceToLatexStringSlice() []string {
	factStrSlice := make([]string, len(s))
	for i := range len(s) {
		factStrSlice[i] = s[i].ToLatexString()
	}
	return factStrSlice
}

func paramInParamSetInFactLatexStringSlice(paramNames []string, paramSets []Fc) []string {
	strSlice := make([]string, len(paramSets))
	for i, paramSet := range paramSets {
		strSlice[i] = fmt.Sprintf("%s $\\in$ %s", toLatexString(paramNames[i]), paramSet.ToLatexString())
	}
	return strSlice
}

func (s *DefExistPropStmt) ToLatexString() string {
	var builder strings.Builder

	builder.WriteString("\\begin{definition}[Existential Proposition]\n")
	builder.WriteString(bodyToLatexString(&s.DefBody.DefHeader, s.DefBody.DomFacts, s.DefBody.IffFacts, true))
	builder.WriteString("\n\\end{definition}")
	return builder.String()
}

func propNameParamsLatexString(propName FcAtom, params []Fc) string {
	var builder strings.Builder
	builder.WriteString(propName.String())
	builder.WriteString("(")
	paramStrSlice := make([]string, len(params))
	for i := range len(params) {
		paramStrSlice[i] = params[i].ToLatexString()
	}
	builder.WriteString(strings.Join(paramStrSlice, ", "))
	builder.WriteString(")")
	return builder.String()
}

func fcParamsLatexString(params []Fc) string {
	paramStrSlice := make([]string, len(params))
	for i := range len(params) {
		paramStrSlice[i] = params[i].ToLatexString()
	}
	return strings.Join(paramStrSlice, ", ")
}

func (s *HaveObjStStmt) ToLatexString() string {
	var builder strings.Builder
	builder.WriteString(fmt.Sprintf("Since existential proposition %s is true", propNameParamsLatexString(s.Fact.PropName, s.Fact.Params)))
	builder.WriteString(" we have ")
	builder.WriteString(fcParamsLatexString(s.Fact.Params))
	builder.WriteString(fmt.Sprintf(" which makes %s true", propNameParamsLatexString(s.Fact.PropName, s.Fact.Params)))
	return builder.String()
}

func (s *ProveInEachCaseStmt) ToLatexString() string {
	var builder strings.Builder
	builder.WriteString("Since ")
	builder.WriteString(s.OrFact.ToLatexString())
	builder.WriteString(" we prove ")
	builder.WriteString(strings.Join(s.ThenFacts.factStmtSliceToLatexStringSlice(), ", "))
	builder.WriteString(glob.KeySymbolColon)
	builder.WriteByte('\n')
	for i := range s.Proofs {
		builder.WriteString(fmt.Sprintf("Case %d: %s\n", i+1, s.OrFact.Facts[i]))
		stmtSlice := make([]string, len(s.Proofs[i]))
		for j, proof := range s.Proofs[i] {
			stmtSlice[j] = proof.ToLatexString()
		}
		builder.WriteString(strings.Join(stmtSlice, ", "))
		builder.WriteString("\n")
	}

	return builder.String()
}

func (s *KnowPropStmt) ToLatexString() string {
	var builder strings.Builder
	builder.WriteString("Assume $\\forall$ ")
	builder.WriteString(strings.Join(paramInParamSetInFactLatexStringSlice(s.Prop.DefHeader.Params, s.Prop.DefHeader.ParamSets), ", "))
	builder.WriteString(strings.Join(s.Prop.IffFacts.factStmtSliceToLatexStringSlice(), ", "))
	builder.WriteString(" we have ")
	builder.WriteString(strings.Join(s.Prop.ThenFacts.factStmtSliceToLatexStringSlice(), ", "))

	builder.WriteString(".")
	builder.WriteString("We call this fact ")
	builder.WriteString(s.Prop.DefHeader.NameWithParamsLatexString())
	builder.WriteString(".")
	return builder.String()
}

func (s *OrStmt) ToLatexString() string {
	factStrSlice := make([]string, len(s.Facts))
	for i := range len(s.Facts) {
		factStrSlice[i] = s.Facts[i].ToLatexString()
	}
	return strings.Join(factStrSlice, "or ")
}

func (s *ImportDirStmt) ToLatexString() string {
	var builder strings.Builder
	builder.WriteString("Import directory ")
	builder.WriteString(s.Path)
	builder.WriteString(" as ")
	builder.WriteString(s.AsPkgName)
	return builder.String()
}

func (s *ImportFileStmt) ToLatexString() string {
	var builder strings.Builder
	builder.WriteString("Import file ")
	builder.WriteString(s.Path)
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
			builder.WriteString(", when ")
			builder.WriteString(strings.Join(domFactStrSlice, ", "))
			builder.WriteString(" ")
		} else {
			builder.WriteString(", when\n\n")
			builder.WriteString(strings.Join(domFactStrSlice, "\n\n"))
			builder.WriteString("\n\n")
		}
	}

	if len(s.UniFact.ThenFacts) > 0 {
		thenFactStrSlice := s.UniFact.ThenFacts.factStmtSliceToLatexStringSlice()
		if ShouldInSingleLineAsLatexString(thenFactStrSlice) {
			builder.WriteString("then ")
			builder.WriteString(strings.Join(thenFactStrSlice, ", "))
			builder.WriteString(" ")
		} else {
			builder.WriteString("then\n\n")
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
	return claimProveBodyToLatexString(s.ClaimProveStmt.ToCheckFact, s.ClaimProveStmt.Proofs, true)
}

func (s *DefFnTemplateStmt) ToLatexString() string {
	var builder strings.Builder
	builder.WriteString("\\begin{definition}[Function Template]\n\n")
	builder.WriteString("We say a function satisfies function template ")
	builder.WriteString(toLatexString(s.FnTemplateStmt.DefHeader.Name))
	builder.WriteString(fmt.Sprintf(" if it satisfies (we use %s here to represent that function):", s.FnTemplateStmt.DefHeader.Name))
	builder.WriteString("\n\n")

	builder.WriteString("It has a domain which is superset of the set which contains parameters satisfying the following properties: ")
	builder.WriteString(strings.Join(paramInParamSetInFactLatexStringSlice(s.FnTemplateStmt.Params, s.FnTemplateStmt.ParamSets), ", "))

	if len(s.FnTemplateStmt.DomFacts) > 0 {
		builder.WriteString(" and ")
		domFactStrSlice := s.FnTemplateStmt.DomFacts.factStmtSliceToLatexStringSlice()
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

	if len(s.FnTemplateStmt.ThenFacts) > 0 {
		builder.WriteString("\n\n")
		builder.WriteString("When its parameters satisfies the above condition, it has the following properties:")
		thenFactStrSlice := s.FnTemplateStmt.ThenFacts.factStmtSliceToLatexStringSlice()
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
	builder.WriteString(s.FnTemplateStmt.RetSet.ToLatexString())

	builder.WriteString("\n\\end{definition}")

	return builder.String()
}

func (s *EnumStmt) ToLatexString() string {
	var builder strings.Builder
	builder.WriteString(s.CurSet.ToLatexString())
	builder.WriteString(" = {")
	builder.WriteString(fcParamsLatexString(s.Items))
	builder.WriteString("}")
	return builder.String()
}

func (s *IntensionalSetStmt) ToLatexString() string {
	var builder strings.Builder
	builder.WriteString(s.CurSet.ToLatexString())
	builder.WriteString(" = {")
	builder.WriteString(s.Param)
	builder.WriteString(" $\\in$ ")
	builder.WriteString(s.ParentSet.ToLatexString())
	builder.WriteString(" | ")
	proofStrSlice := make([]string, len(s.Proofs))
	for i := range len(s.Proofs) {
		proofStrSlice[i] = s.Proofs[i].ToLatexString()
	}
	builder.WriteString(strings.Join(proofStrSlice, ", "))
	builder.WriteString("}")
	return builder.String()
}

func (s *ClaimPropStmt) ToLatexString() string {
	var builder strings.Builder

	builder.WriteString(s.ToProp().ToLatexString())

	builder.WriteString("\n\n")

	builder.WriteString(claimProveBodyToLatexString(s.ToUniFact(), s.Proofs, s.IsProve))

	return builder.String()
}

func (s *ClaimExistPropStmt) ToLatexString() string {
	return "ClaimExistPropStmt latex to be implemented"
}

func (s *ProveByMathInductionStmt) ToLatexString() string {
	var builder strings.Builder
	builder.WriteString("By mathematical induction, we have ")
	builder.WriteString(s.Fact.String())

	indexFc := s.Fact.Params[s.ParamIndex]

	builder.WriteString(fmt.Sprintf("%s is true $\\forall$ %s $\\geq$ %d", s.Fact.ToLatexString(), indexFc.ToLatexString(), s.Start))
	builder.WriteString(".")

	return builder.String()
}

func (s *ProveOverFiniteSetStmt) ToLatexString() string {
	var builder strings.Builder
	builder.WriteString("We prove that by iterating over the elements of the finite set(s): ")
	builder.WriteString(strings.Join(paramInParamSetInFactLatexStringSlice(s.Fact.Params, s.Fact.ParamSets), ", "))
	builder.WriteString(". ")
	builder.WriteString(s.Fact.ToLatexString())
	builder.WriteString(".\n")
	builder.WriteString("[Proof] ")
	proofStrSlice := make([]string, len(s.Proofs))
	for i := range len(s.Proofs) {
		proofStrSlice[i] = s.Proofs[i].ToLatexString()
	}
	builder.WriteString(strings.Join(proofStrSlice, ", "))

	return builder.String()
}

func (s *HaveObjInNonEmptySetStmt) ToLatexString() string {
	var builder strings.Builder
	builder.WriteString("We have objects from nonempty set(s): ")
	builder.WriteString(strings.Join(paramInParamSetInFactLatexStringSlice(s.Objs, s.ObjSets), ", "))
	builder.WriteString(".")
	return builder.String()
}

func (s *HaveSetStmt) ToLatexString() string {
	var builder strings.Builder
	builder.WriteString("We have a set: ")
	builder.WriteString(s.Fact.String())
	builder.WriteString(".")
	return builder.String()
}

func (s *HaveSetFnStmt) ToLatexString() string {
	var builder strings.Builder
	builder.WriteString("We have a function returning a set: ")
	builder.WriteString(s.DefHeader.NameWithParamsLatexString())
	builder.WriteString(".")
	return builder.String()
}

func (s *HaveSetDefinedByReplacementStmt) ToLatexString() string {
	var builder strings.Builder
	builder.WriteString("We have a set by axiom of replacement: ")
	builder.WriteString(s.Name)
	builder.WriteString(" = {")
	builder.WriteString("y $\\in$ ")
	builder.WriteString(s.DomSet.ToLatexString())
	builder.WriteString(" | there exists x st ")
	builder.WriteString(s.PropName.String())
	builder.WriteString("(x, y) is true.")
	builder.WriteString("}")
	return builder.String()
}

func (s *NamedUniFactStmt) ToLatexString() string {
	var builder strings.Builder
	builder.WriteString("$\\forall$ ")
	builder.WriteString(strings.Join(paramInParamSetInFactLatexStringSlice(s.DefPropStmt.DefHeader.Params, s.DefPropStmt.DefHeader.ParamSets), ", "))
	builder.WriteString(" then ")
	builder.WriteString(strings.Join(s.DefPropStmt.ThenFacts.factStmtSliceToLatexStringSlice(), ", "))
	builder.WriteString(".")
	builder.WriteString("We call this fact ")
	builder.WriteString(s.DefPropStmt.DefHeader.NameWithParamsLatexString())
	builder.WriteString(".")
	return builder.String()
}

func (s *FnTemplateStmt) ToLatexString() string {
	return NewFnTemplateDefStmt(s).ToLatexString()
}

func (s FcSlice) fcSliceToLatexStringSlice() []string {
	fcStrSlice := make([]string, len(s))
	for i := range len(s) {
		fcStrSlice[i] = s[i].ToLatexString()
	}
	return fcStrSlice
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
	defExistProp := NewDefExistPropStmt(&s.ExistProp.DefBody, s.ExistProp.ExistParams, s.ExistProp.ExistParamSets)
	builder.WriteString(defExistProp.ToLatexString())

	builder.WriteString("\n\n")
	builder.WriteString("We assume existential proposition is true for all parameters in the proposition's domain.")

	return builder.String()
}
