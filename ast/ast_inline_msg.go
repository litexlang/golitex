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

func (stmt *DefLetStmt) InlineString() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordLet)
	builder.WriteString(" ")
	builder.WriteString(StrFcSetPairs(stmt.Objs, stmt.ObjSets))
	builder.WriteString(glob.KeySymbolColon)
	builder.WriteString(inlineFactsString(stmt.Facts))
	return builder.String()
}
func (c *DefPropStmt) InlineString() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordProp)
	builder.WriteString(" ")
	builder.WriteString(string(c.DefHeader.Name))
	if len(c.DomFacts) > 0 {
		builder.WriteString(glob.KeySymbolColon)
		builder.WriteString(inlineFactsString(c.DomFacts))
	}
	if len(c.IffFacts) > 0 {
		builder.WriteString(glob.KeySymbolEquivalent)
		builder.WriteString(inlineFactsString(c.IffFacts))
	}
	if len(c.ThenFacts) > 0 {
		builder.WriteString(glob.KeySymbolRightArrow)
		builder.WriteString(inlineFactsString(c.ThenFacts))
	}
	return builder.String()
}
func (l *DefFnStmt) InlineString() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordFn)
	builder.WriteString(" ")
	builder.WriteString(NewDefHeader(FcAtom(l.Name), l.FnTemplate.Params, l.FnTemplate.ParamSets).StringWithoutColonAtEnd())
	builder.WriteString(" ")
	builder.WriteString(l.FnTemplate.RetSet.String())
	if len(l.FnTemplate.DomFacts) > 0 {
		builder.WriteString(glob.KeySymbolColon)
		builder.WriteString(inlineFactsString(l.FnTemplate.DomFacts))
	}
	if len(l.FnTemplate.ThenFacts) > 0 {
		builder.WriteString(glob.KeySymbolRightArrow)
		builder.WriteString(inlineFactsString(l.FnTemplate.ThenFacts))
	}

	return builder.String()
}
func (l *UniFactStmt) InlineString() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordForall)
	builder.WriteString(" ")
	builder.WriteString(StrFcSetPairs(l.Params, l.ParamSets))
	if len(l.DomFacts) > 0 {
		builder.WriteString(glob.KeySymbolColon)
		builder.WriteString(inlineFactsString(l.DomFacts))
	}
	if len(l.ThenFacts) > 0 {
		builder.WriteString(glob.KeySymbolRightArrow)
		builder.WriteString(inlineFactsString(l.ThenFacts))
	}
	return builder.String()
}

func (p *SpecFactStmt) InlineString() string {
	return p.String()
}

func (f *ClaimProveStmt) InlineString() string {
	return f.String()
}
func (f *KnowFactStmt) InlineString() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordKnow)
	builder.WriteString(" ")
	builder.WriteString(inlineCanBeKnownFactsString(f.Facts))
	return builder.String()
}

func (s *DefExistPropStmt) InlineString() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordExistProp)
	builder.WriteString(" ")
	builder.WriteString(StrFcSetPairs(s.ExistParams, s.ExistParamSets))
	builder.WriteString(" ")
	builder.WriteString(glob.KeywordSt)
	builder.WriteString(" ")
	builder.WriteString(s.DefBody.DefHeader.InlineString())

	if len(s.DefBody.DomFacts) > 0 {
		builder.WriteString(glob.KeySymbolColon)
		builder.WriteString(inlineFactsString(s.DefBody.DomFacts))
	}

	if len(s.DefBody.IffFacts) > 0 {
		builder.WriteString(glob.KeySymbolEquivalent)
		builder.WriteString(inlineFactsString(s.DefBody.IffFacts))
	}

	return builder.String()
}

func (s *HaveObjStStmt) InlineString() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordHave)
	builder.WriteString(" ")
	builder.WriteString(strings.Join(s.ObjNames, ", "))
	builder.WriteString(" ")
	builder.WriteString(glob.KeywordSt)
	builder.WriteString(" ")
	builder.WriteString(s.Fact.InlineString())
	return builder.String()
}

func (s *ProveInEachCaseStmt) InlineString() string { return s.String() }
func (s *KnowPropStmt) InlineString() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordKnow)
	builder.WriteString(" ")
	builder.WriteString(glob.KeySymbolAt)
	builder.WriteString(s.Prop.InlineString())
	return builder.String()
}

func (s *OrStmt) InlineString() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordOr)
	builder.WriteString(glob.KeySymbolLeftBrace)
	orFactStrSlice := make([]string, len(s.Facts))
	for i, orFact := range s.Facts {
		orFactStrSlice[i] = orFact.InlineString()
	}
	builder.WriteString(strings.Join(orFactStrSlice, ", "))
	builder.WriteString(glob.KeySymbolRightBrace)
	return builder.String()
}

func (s *ImportDirStmt) InlineString() string {
	return s.String()
}

func (s *ImportFileStmt) InlineString() string {
	return s.String()
}
func (s *ProveStmt) InlineString() string {
	return s.String()
}
func (s *UniFactWithIffStmt) InlineString() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordForall)
	builder.WriteString(" ")
	builder.WriteString(StrFcSetPairs(s.UniFact.Params, s.UniFact.ParamSets))
	builder.WriteString(glob.KeySymbolColon)
	if len(s.UniFact.DomFacts) > 0 {
		builder.WriteString(inlineFactsString(s.UniFact.DomFacts))
	}
	if len(s.UniFact.ThenFacts) > 0 {
		builder.WriteString(glob.KeySymbolRightArrow)
		builder.WriteString(inlineFactsString(s.UniFact.ThenFacts))
	}
	if len(s.IffFacts) > 0 {
		builder.WriteString(glob.KeySymbolEquivalent)
		builder.WriteString(inlineFactsString(s.IffFacts))
	}
	return builder.String()
}
func (s *ClaimProveByContradictionStmt) InlineString() string { panic("") }
func (s *EnumStmt) InlineString() string                      { panic("") }
func (s *IntensionalSetStmt) InlineString() string            { panic("") }
func (s *ClaimPropStmt) InlineString() string                 { panic("") }
func (s *ClaimExistPropStmt) InlineString() string            { panic("") }

// func (s *ProveByMathInductionStmt) InlineString() string        { panic("") }
func (s *ProveByEnumStmt) InlineString() string                 { panic("") }
func (s *HaveObjInNonEmptySetStmt) InlineString() string        { panic("") }
func (s *HaveEnumSetStmt) InlineString() string                 { panic("") }
func (s *HaveIntensionalSetStmt) InlineString() string          { panic("") }
func (s *HaveSetFnStmt) InlineString() string                   { panic("") }
func (s *HaveSetDefinedByReplacementStmt) InlineString() string { panic("") }
func (s *NamedUniFactStmt) InlineString() string                { panic("") }

func (s *EqualsFactStmt) InlineString() string {
	var builder strings.Builder
	builder.WriteString(glob.KeySymbolEqual)
	builder.WriteString(glob.KeySymbolLeftBrace)
	fcSlice := make([]string, len(s.Params))
	for i, param := range s.Params {
		fcSlice[i] = param.String()
	}
	builder.WriteString(strings.Join(fcSlice, ", "))
	builder.WriteString(glob.KeySymbolRightBrace)
	return builder.String()
}

func (s *KnowExistPropStmt) InlineString() string { panic("") }
func (s *LatexStmt) InlineString() string         { panic("") }
func (s *FnTemplateDefStmt) InlineString() string { panic("") }
func (s *ClearStmt) InlineString() string         { return s.String() }
func (s *InlineFactsStmt) InlineString() string   { return inlineFactsString(s.Facts) }
func (s *ProveByInductionStmt) InlineString() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordProveByInduction)
	builder.WriteString(glob.KeySymbolColon)
	builder.WriteString(s.Fact.InlineString())
	builder.WriteString(", ")
	builder.WriteString(s.Param)
	builder.WriteString(", ")
	builder.WriteString(s.Start.String())
	return builder.String()
}

func inlineFactsString(facts FactStmtSlice) string {
	var builder strings.Builder
	for i := range len(facts) - 1 {
		switch asFact := facts[i].(type) {
		case *UniFactStmt:
			builder.WriteString(asFact.InlineString())
			builder.WriteString("; ")
		default:
			builder.WriteString(asFact.InlineString())
			builder.WriteString(", ")
		}
	}
	switch asFact := facts[len(facts)-1].(type) {
	case *UniFactStmt:
		builder.WriteString(asFact.InlineString())
		builder.WriteString(";")
	default:
		builder.WriteString(asFact.InlineString())
	}
	return builder.String()
}

func inlineCanBeKnownFactsString(facts CanBeKnownStmtSlice) string {
	var builder strings.Builder
	for i := range len(facts) - 1 {
		switch asFact := facts[i].(type) {
		case *UniFactStmt:
			builder.WriteString(asFact.InlineString())
			builder.WriteString("; ")
		default:
			builder.WriteString(asFact.InlineString())
			builder.WriteString(", ")
		}
	}
	switch asFact := facts[len(facts)-1].(type) {
	case *UniFactStmt:
		builder.WriteString(asFact.InlineString())
		builder.WriteString(";")
	default:
		builder.WriteString(asFact.InlineString())
	}
	return builder.String()
}

func (header *DefHeader) InlineString() string {
	var builder strings.Builder
	builder.WriteString(header.Name.String())
	builder.WriteString("(")
	builder.WriteString(StrFcSetPairs(header.Params, header.ParamSets))
	builder.WriteString(")")
	return builder.String()
}

func (s *HaveObjEqualStmt) InlineString() string {
	return s.String()
}

func (s *HaveFnEqualStmt) InlineString() string {
	return s.String()
}

func (s *HaveFnLiftStmt) InlineString() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordHave)
	builder.WriteString(" ")
	builder.WriteString(glob.KeywordFn)
	builder.WriteString(" ")
	builder.WriteString(s.FnName)
	builder.WriteString(" ")
	builder.WriteString(glob.KeySymbolEqual)
	builder.WriteString(" ")
	builder.WriteString(glob.KeywordLift)
	builder.WriteString(glob.KeySymbolLeftBrace)
	strSlice := []string{s.Opt.String()}
	for _, param := range s.DomainOfEachParamOfGivenFn {
		strSlice = append(strSlice, param.String())
	}
	builder.WriteString(strings.Join(strSlice, ", "))
	builder.WriteString(glob.KeySymbolRightBrace)

	return builder.String()
}

func (s *HaveFnStmt) InlineString() string {
	return "TODO"
}

func (s *MarkdownStmt) InlineString() string {
	return s.Markdown
}

func (s *ClaimIffStmt) InlineString() string {
	return "TODO"
}

func (s *ProveInRangeStmt) InlineString() string {
	return "TODO"
}

func (s *ProveIsTransitivePropStmt) InlineString() string {
	return "TODO"
}

func (s *ProveIsCommutativePropStmt) InlineString() string {
	return "TODO"
}

func (s *AlgoIfStmt) InlineString() string {
	return "TODO"
}

func (s *AlgoReturnStmt) InlineString() string {
	return "TODO"
}

func (s *AlgoDefStmt) InlineString() string {
	return "TODO"
}

func (s *EvalStmt) InlineString() string {
	return fmt.Sprintf("%s %s", glob.KeywordEval, s.Value.String())
}
