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

func (stmt *DefObjStmt) InlineString() string                 { panic("") }
func (c *DefPropStmt) InlineString() string                   { panic("") }
func (l *DefFnStmt) InlineString() string                     { panic("") }
func (l *UniFactStmt) InlineString() string                   { panic("") }
func (p *SpecFactStmt) InlineString() string                  { panic("") }
func (f *ClaimProveStmt) InlineString() string                { panic("") }
func (f *KnowFactStmt) InlineString() string                  { panic("") }
func (s *DefExistPropStmt) InlineString() string              { panic("") }
func (s *HaveObjStStmt) InlineString() string                 { panic("") }
func (s *ProveInEachCaseStmt) InlineString() string           { panic("") }
func (s *KnowPropStmt) InlineString() string                  { panic("") }
func (s *OrStmt) InlineString() string                        { panic("") }
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
func (s *EqualsFactStmt) InlineString() string                  { panic("") }
func (s *KnowExistPropStmt) InlineString() string               { panic("") }
func (s *CommentStmt) InlineString() string                     { panic("") }
func (s *FnTemplateDefStmt) InlineString() string               { panic("") }
func (s *ClearStmt) InlineString() string                       { panic("") }
func (s *InlineFactsStmt) InlineString() string                 { panic("") }
func (s *ProveByInductionStmt) InlineString() string            { panic("") }
