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

func strFcSetPairsLatexString(objs []string, objSets []Fc) string {
	pairStrSlice := make([]string, len(objs))
	for i := range len(objs) {
		pairStrSlice[i] = fmt.Sprintf("%s \\in %s", objs[i], objSets[i])
	}
	return strings.Join(pairStrSlice, ", ")
}

func (s *DefObjStmt) ToLatexString() string {
	var builder strings.Builder

	builder.WriteString("Suppose we have objects: ")
	builder.WriteString(strFcSetPairsLatexString(s.Objs, s.ObjSets))
	builder.WriteString(".")

	if len(s.Facts) > 0 {
		builder.WriteString("And the following facts: ")
		factStrSlice := make([]string, len(s.Facts))
		for i := range len(s.Facts) {
			factStrSlice[i] = s.Facts[i].ToLatexString()
		}
		builder.WriteString(strings.Join(factStrSlice, ", "))
		builder.WriteString(".")
	}

	return builder.String()
}

func (head DefHeader) ToLatexString() string {
	var builder strings.Builder
	builder.WriteString(head.Name)
	builder.WriteString("(")
	builder.WriteString(strFcSetPairsLatexString(head.Params, head.ParamSets))
	builder.WriteString(")")
	return builder.String()
}

func (head DefHeader) NameWithParamsLatexString() string {
	var builder strings.Builder
	builder.WriteString(head.Name)
	builder.WriteString("(")
	builder.WriteString(strings.Join(head.Params, ", "))
	builder.WriteString(")")
	return builder.String()
}

func (c *DefPropStmt) ToLatexString() string {
	var builder strings.Builder

	builder.WriteString("[Definition] Proposition ")
	builder.WriteString(c.DefHeader.ToLatexString())
	builder.WriteString(".")

	if len(c.DomFacts) == 0 && len(c.IffFacts) == 0 {
		return builder.String()
	}

	if len(c.DomFacts) > 0 {
		builder.WriteString(" \\text{When}:")
		domFactStrSlice := make([]string, len(c.DomFacts))
		for i := range len(c.DomFacts) {
			domFactStrSlice[i] = c.DomFacts[i].ToLatexString()
		}
		builder.WriteString(strings.Join(domFactStrSlice, ", "))
		builder.WriteString(".")
	}

	if len(c.IffFacts) > 0 {
		builder.WriteString(fmt.Sprintf("We say %s \\text{Iff}:", c.DefHeader.NameWithParamsLatexString()))
		iffFactStrSlice := make([]string, len(c.IffFacts))
		for i := range len(c.IffFacts) {
			iffFactStrSlice[i] = c.IffFacts[i].ToLatexString()
		}
		builder.WriteString(strings.Join(iffFactStrSlice, ", "))
		builder.WriteString(".")
	}

	return builder.String()
}

func (l *DefFnStmt) ToLatexString() string {
	var builder strings.Builder

	builder.WriteString("Suppose we have a function: ")
	builder.WriteString(l.FnTemplateStmt.DefHeader.NameWithParamsLatexString())
	builder.WriteString(".")

	if len(l.FnTemplateStmt.DomFacts) == 0 && len(l.FnTemplateStmt.ThenFacts) == 0 {
		return builder.String()
	}

	if len(l.FnTemplateStmt.DomFacts) > 0 {
		builder.WriteString("Its domain is: ")
		domFactStrSlice := make([]string, len(l.FnTemplateStmt.DomFacts))
		for i := range len(l.FnTemplateStmt.DomFacts) {
			domFactStrSlice[i] = l.FnTemplateStmt.DomFacts[i].ToLatexString()
		}
		builder.WriteString(strings.Join(domFactStrSlice, ", "))
		builder.WriteString(".")
	}

	if len(l.FnTemplateStmt.ThenFacts) > 0 {
		builder.WriteString("We also suppose the function has the following properties: ")
		thenFactStrSlice := make([]string, len(l.FnTemplateStmt.ThenFacts))
		for i := range len(l.FnTemplateStmt.ThenFacts) {
			thenFactStrSlice[i] = l.FnTemplateStmt.ThenFacts[i].ToLatexString()
		}
		builder.WriteString(strings.Join(thenFactStrSlice, ", "))
		builder.WriteString(".")
	}

	return builder.String()
}

func (l *UniFactStmt) ToLatexString() string {
	var builder strings.Builder
	builder.WriteString("\\forall ")
	paramSetFacts := l.ParamInParamSet()
	for _, paramSetFact := range paramSetFacts {
		builder.WriteString(paramSetFact.ToLatexString())
		builder.WriteString(", ")
	}
	builder.WriteString("when ")
	for _, domFact := range l.DomFacts {
		builder.WriteString(domFact.ToLatexString())
		builder.WriteString(", ")
	}
	builder.WriteString("then ")
	thenFactToLatexStr := []string{}
	for _, fact := range l.ThenFacts {
		thenFactToLatexStr = append(thenFactToLatexStr, fact.ToLatexString())
	}
	builder.WriteString(strings.Join(thenFactToLatexStr, ", "))
	builder.WriteString(".")
	return builder.String()
}

func (p *SpecFactStmt) ToLatexString() string {
	str := p.String()
	str = strings.TrimPrefix(str, glob.KeySymbolDollar)
	return str
}

func (f *ClaimProveStmt) ToLatexString() string {
	var builder strings.Builder

	builder.WriteString("We claim that ")
	builder.WriteString(f.ToCheckFact.ToLatexString())
	builder.WriteString(".")

	if len(f.Proofs) > 0 {
		builder.WriteString("[Proof] ")
		proofStrSlice := make([]string, len(f.Proofs))
		for i := range len(f.Proofs) {
			proofStrSlice[i] = f.Proofs[i].ToLatexString()
		}
		builder.WriteString(strings.Join(proofStrSlice, ", "))
		builder.WriteString(".")
	}

	return builder.String()
}
func (f *KnowFactStmt) ToLatexString() string {
	var builder strings.Builder
	builder.WriteString("Assume ")

	if len(f.Facts) > 1 {
		builder.WriteString(glob.KeySymbolColon)
		builder.WriteByte('\n')

		factStrSlice := make([]string, len(f.Facts))
		for i := range len(f.Facts) {
			factStrSlice[i] = glob.SplitLinesAndAdd4NIndents(f.Facts[i].ToLatexString(), 1)
		}
		builder.WriteString(strings.Join(factStrSlice, "\n"))
		return builder.String()
	} else {
		builder.WriteString(" ")
		builder.WriteString(f.Facts[0].ToLatexString())
		return builder.String()
	}
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
		strSlice[i] = fmt.Sprintf("%s \\in %s", paramNames[i], paramSet.ToLatexString())
	}
	return strSlice
}

func (s *DefExistPropStmt) ToLatexString() string {
	var builder strings.Builder

	builder.WriteString("[Definition] Existential Proposition: When ")
	paramCondStrSlice := paramInParamSetInFactLatexStringSlice(s.DefBody.DefHeader.Params, s.DefBody.DefHeader.ParamSets)
	paramCondStrSlice = append(paramCondStrSlice, s.DefBody.DomFacts.factStmtSliceToLatexStringSlice()...)

	builder.WriteString(strings.Join(paramCondStrSlice, ", "))

	builder.WriteString(", we say ")
	builder.WriteString(s.DefBody.DefHeader.NameWithParamsLatexString())
	builder.WriteString(" \\text{Iff}: there exist ")

	existParamInFactStrSlice := paramInParamSetInFactLatexStringSlice(s.ExistParams, s.ExistParamSets)
	builder.WriteString(strings.Join(existParamInFactStrSlice, ", "))
	builder.WriteString(" st ")

	builder.WriteString(strings.Join(s.DefBody.IffFacts.factStmtSliceToLatexStringSlice(), ", "))
	builder.WriteString(".")

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
	builder.WriteString("Assume forall ")
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

func (s *KnowExistPropStmt) ToLatexString() string {
	return "knowExistPropStmt latex to be implemented"
}

func (s *OrStmt) ToLatexString() string {
	factStrSlice := make([]string, len(s.Facts))
	for i := range len(s.Facts) {
		factStrSlice[i] = s.Facts[i].ToLatexString()
	}
	return strings.Join(factStrSlice, "\\text{or} ")
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
	builder.WriteString("[Example] ")
	stmtSlice := make([]string, len(s.Proof))
	for i := range s.Proof {
		stmtSlice[i] = s.Proof[i].ToLatexString()
	}
	builder.WriteString(strings.Join(stmtSlice, ", "))
	builder.WriteString(".")
	return builder.String()
}

func (s *UniFactWithIffStmt) ToLatexString() string {
	var builder strings.Builder
	builder.WriteString(strings.Join(paramInParamSetInFactLatexStringSlice(s.UniFact.Params, s.UniFact.ParamSets), ", "))

	if len(s.UniFact.DomFacts) > 0 {
		builder.WriteString(" \\text{When}: ")
		builder.WriteString(strings.Join(s.UniFact.DomFacts.factStmtSliceToLatexStringSlice(), ", "))
	}

	builder.WriteString(" \\text{then}: ")

	builder.WriteString(strings.Join(s.UniFact.ThenFacts.factStmtSliceToLatexStringSlice(), ", "))

	builder.WriteString(" \\text{Iff}: ")
	builder.WriteString(strings.Join(s.IffFacts.factStmtSliceToLatexStringSlice(), ", "))

	builder.WriteString(".")
	return builder.String()
}

func (s StmtSlice) stmtSliceToLatexStringSlice() []string {
	stmtStrSlice := make([]string, len(s))
	for i := range len(s) {
		stmtStrSlice[i] = s[i].ToLatexString()
	}
	return stmtStrSlice
}

func (s *ClaimProveByContradictionStmt) ToLatexString() string {
	var builder strings.Builder
	builder.WriteString("We claim that ")
	builder.WriteString(s.ClaimProveStmt.ToCheckFact.ToLatexString())
	builder.WriteString(".\n")
	builder.WriteString("[Proof By Contradiction] ")
	builder.WriteString(strings.Join(s.ClaimProveStmt.Proofs.stmtSliceToLatexStringSlice(), ", "))
	return builder.String()
}

func (s *DefFnTemplateStmt) ToLatexString() string {
	var builder strings.Builder
	builder.WriteString("Suppose we have a set of functions: ")
	builder.WriteString("their parameters satisfy condition: ")
	builder.WriteString(strings.Join(paramInParamSetInFactLatexStringSlice(s.FnTemplateStmt.Params, s.FnTemplateStmt.ParamSets), ", "))
	builder.WriteString(" \\text{and} ")
	builder.WriteString(strings.Join(s.FnTemplateStmt.DomFacts.factStmtSliceToLatexStringSlice(), ", "))
	builder.WriteString("When their parameters satisfies the above condition, they have the following properties: ")
	builder.WriteString(strings.Join(s.FnTemplateStmt.ThenFacts.factStmtSliceToLatexStringSlice(), ", "))
	builder.WriteString(".")
	return builder.String()
}

func (s *EnumStmt) ToLatexString() string {
	var builder strings.Builder
	builder.WriteString("set ")
	builder.WriteString(s.CurSet.ToLatexString())
	builder.WriteString(" = {")
	builder.WriteString(fcParamsLatexString(s.Items))
	builder.WriteString("}")
	return builder.String()
}

func (s *IntensionalSetStmt) ToLatexString() string {
	var builder strings.Builder
	builder.WriteString("set ")
	builder.WriteString(s.CurSet.ToLatexString())
	builder.WriteString(" = {")
	builder.WriteString(s.Param)
	builder.WriteString(" \\in ")
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
	builder.WriteString("We claim that forall ")
	builder.WriteString(strings.Join(paramInParamSetInFactLatexStringSlice(s.Prop.DefHeader.Params, s.Prop.DefHeader.ParamSets), ", "))
	builder.WriteString(" we have ")
	builder.WriteString(strings.Join(s.Prop.ThenFacts.factStmtSliceToLatexStringSlice(), ", "))
	builder.WriteString(".")
	builder.WriteString("we call this fact ")
	builder.WriteString(s.Prop.DefHeader.NameWithParamsLatexString())
	builder.WriteString(".")
	builder.WriteByte('\n')

	if s.IsProve {
		builder.WriteString("[Proof] ")
	} else {
		builder.WriteString("[Proof By Contradiction] ")
	}

	proofStrSlice := make([]string, len(s.Proofs))
	for i := range len(s.Proofs) {
		proofStrSlice[i] = s.Proofs[i].ToLatexString()
	}
	builder.WriteString(strings.Join(proofStrSlice, ", "))
	return builder.String()
}

func (s *ClaimExistPropStmt) ToLatexString() string {
	return "ClaimExistPropStmt latex to be implemented"
}

func (s *ProveByMathInductionStmt) ToLatexString() string {
	var builder strings.Builder
	builder.WriteString("By mathematical induction, we have ")
	builder.WriteString(s.PropName.String())
	builder.WriteString("(i) is true \\forall i \\geq ")
	builder.WriteString(s.Start.ToLatexString())
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
func (s *HaveObjInNonEmptySetStmt) ToLatexString() string { return "" }

func (s *HaveSetStmt) ToLatexString() string { return "" }

func (s *HaveSetFnStmt) ToLatexString() string { return "" }

func (s *HaveSetDefinedByReplacementStmt) ToLatexString() string { return "" }

func (s *NamedUniFactStmt) ToLatexString() string { return "" }

func (s *FnTemplateStmt) ToLatexString() string { return "" }
