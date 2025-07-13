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

func (s *DefObjStmt) ToLatexString() string  { return "" }
func (c *DefPropStmt) ToLatexString() string { return "" }
func (l *DefFnStmt) ToLatexString() string   { return "" }
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
func (p *SpecFactStmt) ToLatexString() string   { return "" }
func (f *ClaimProveStmt) ToLatexString() string { return "" }
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
func (s *DefExistPropStmt) ToLatexString() string                { return "" }
func (s *HaveObjStStmt) ToLatexString() string                   { return "" }
func (s *ProveInEachCaseStmt) ToLatexString() string             { return "" }
func (s *KnowPropStmt) ToLatexString() string                    { return "" }
func (s *KnowExistPropStmt) ToLatexString() string               { return "" }
func (s *OrStmt) ToLatexString() string                          { return "" }
func (s *ImportDirStmt) ToLatexString() string                   { return "" }
func (s *ImportFileStmt) ToLatexString() string                  { return "" }
func (s *ProveStmt) ToLatexString() string                       { return "" }
func (s *UniFactWithIffStmt) ToLatexString() string              { return "" }
func (s *ClaimProveByContradictionStmt) ToLatexString() string   { return "" }
func (s *DefFnTemplateStmt) ToLatexString() string               { return "" }
func (s *EnumStmt) ToLatexString() string                        { return "" }
func (s *IntensionalSetStmt) ToLatexString() string              { return "" }
func (s *ClaimPropStmt) ToLatexString() string                   { return "" }
func (s *ClaimExistPropStmt) ToLatexString() string              { return "" }
func (s *ProveByMathInductionStmt) ToLatexString() string        { return "" }
func (s *ProveOverFiniteSetStmt) ToLatexString() string          { return "" }
func (s *HaveObjInNonEmptySetStmt) ToLatexString() string        { return "" }
func (s *HaveSetStmt) ToLatexString() string                     { return "" }
func (s *HaveSetFnStmt) ToLatexString() string                   { return "" }
func (s *HaveSetDefinedByReplacementStmt) ToLatexString() string { return "" }
func (s *NamedUniFactStmt) ToLatexString() string                { return "" }
