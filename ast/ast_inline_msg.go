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
	glob "golitex/glob"
	"strings"
)

func (stmt *DefObjStmt) InlineString() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordLet)
	builder.WriteString(" ")
	builder.WriteString(strFcSetPairs(stmt.Objs, stmt.ObjSets))
	builder.WriteString(glob.KeySymbolColon)
	builder.WriteString(inlineFactsString(stmt.Facts))
	return builder.String()
}
func (c *DefPropStmt) InlineString() string { panic("") }
func (l *DefFnStmt) InlineString() string   { panic("") }
func (l *UniFactStmt) InlineString() string { panic("") }

func (p *SpecFactStmt) InlineString() string {
	return p.String()
}

func (f *ClaimProveStmt) InlineString() string { panic("") }
func (f *KnowFactStmt) InlineString() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordKnow)
	builder.WriteString(" ")
	builder.WriteString(inlineCanBeKnownFactsString(f.Facts))
	return builder.String()
}

func (s *DefExistPropStmt) InlineString() string    { panic("") }
func (s *HaveObjStStmt) InlineString() string       { panic("") }
func (s *ProveInEachCaseStmt) InlineString() string { return s.String() }
func (s *KnowPropStmt) InlineString() string        { panic("") }

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

func (s *ImportDirStmt) InlineString() string                 { panic("") }
func (s *ImportFileStmt) InlineString() string                { panic("") }
func (s *ProveStmt) InlineString() string                     { panic("") }
func (s *UniFactWithIffStmt) InlineString() string            { panic("") }
func (s *ClaimProveByContradictionStmt) InlineString() string { panic("") }
func (s *EnumStmt) InlineString() string                      { panic("") }
func (s *IntensionalSetStmt) InlineString() string            { panic("") }
func (s *ClaimPropStmt) InlineString() string                 { panic("") }
func (s *ClaimExistPropStmt) InlineString() string            { panic("") }

// func (s *ProveByMathInductionStmt) InlineString() string        { panic("") }
func (s *ProveOverFiniteSetStmt) InlineString() string          { panic("") }
func (s *HaveObjInNonEmptySetStmt) InlineString() string        { panic("") }
func (s *HaveSetStmt) InlineString() string                     { panic("") }
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

func (s *KnowExistPropStmt) InlineString() string    { panic("") }
func (s *CommentStmt) InlineString() string          { panic("") }
func (s *FnTemplateDefStmt) InlineString() string    { panic("") }
func (s *ClearStmt) InlineString() string            { panic("") }
func (s *InlineFactsStmt) InlineString() string      { return inlineFactsString(s.Facts) }
func (s *ProveByInductionStmt) InlineString() string { panic("") }

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
	builder.WriteString(strFcSetPairs(header.Params, header.ParamSets))
	builder.WriteString(")")
	return builder.String()
}
