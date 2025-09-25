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

type Stmt interface {
	stmt()
	String() string
	ToLatexString() string
	InlineString() string
	GetLine() uint
}

func (s *DefObjStmt) stmt()                      {}
func (s *DefPropStmt) stmt()                     {}
func (s *DefFnStmt) stmt()                       {}
func (s *UniFactStmt) stmt()                     {}
func (s *SpecFactStmt) stmt()                    {}
func (s *ClaimProveStmt) stmt()                  {}
func (s *KnowFactStmt) stmt()                    {}
func (s *DefExistPropStmt) stmt()                {}
func (s *HaveObjStStmt) stmt()                   {}
func (s *ProveInEachCaseStmt) stmt()             {}
func (s *KnowPropStmt) stmt()                    {}
func (s *OrStmt) stmt()                          {}
func (s *ImportDirStmt) stmt()                   {}
func (s *ImportFileStmt) stmt()                  {}
func (s *ProveStmt) stmt()                       {}
func (s *UniFactWithIffStmt) stmt()              {}
func (s *ClaimProveByContradictionStmt) stmt()   {}
func (s *EnumStmt) stmt()                        {}
func (s *IntensionalSetStmt) stmt()              {}
func (s *ClaimPropStmt) stmt()                   {}
func (s *ClaimExistPropStmt) stmt()              {}
func (s *ProveOverFiniteSetStmt) stmt()          {}
func (s *HaveObjInNonEmptySetStmt) stmt()        {}
func (s *HaveSetStmt) stmt()                     {}
func (s *HaveSetFnStmt) stmt()                   {}
func (s *HaveSetDefinedByReplacementStmt) stmt() {}
func (s *NamedUniFactStmt) stmt()                {}
func (s *EqualsFactStmt) stmt()                  {}
func (s *KnowExistPropStmt) stmt()               {}
func (s *CommentStmt) stmt()                     {}
func (s *FnTemplateDefStmt) stmt()               {}
func (s *ClearStmt) stmt()                       {}
func (s *InlineFactsStmt) stmt()                 {}
func (s *ProveByInductionStmt) stmt()            {}
func (s *HaveObjEqualStmt) stmt()                {}
func (s *HaveFnEqualStmt) stmt()                 {}
func (s *HaveFnLiftStmt) stmt()                  {}
func (s *HaveFnStmt) stmt()                      {}

func (s *DefObjStmt) GetLine() uint                      { return s.Line }
func (s *DefPropStmt) GetLine() uint                     { return s.Line }
func (s *DefFnStmt) GetLine() uint                       { return s.Line }
func (s *UniFactStmt) GetLine() uint                     { return s.Line }
func (s *SpecFactStmt) GetLine() uint                    { return s.Line }
func (s *ClaimProveStmt) GetLine() uint                  { return s.Line }
func (s *KnowFactStmt) GetLine() uint                    { return s.Line }
func (s *DefExistPropStmt) GetLine() uint                { return s.Line }
func (s *HaveObjStStmt) GetLine() uint                   { return s.Line }
func (s *ProveInEachCaseStmt) GetLine() uint             { return s.Line }
func (s *KnowPropStmt) GetLine() uint                    { return s.Line }
func (s *OrStmt) GetLine() uint                          { return s.Line }
func (s *ImportDirStmt) GetLine() uint                   { return s.Line }
func (s *ImportFileStmt) GetLine() uint                  { return s.Line }
func (s *ProveStmt) GetLine() uint                       { return s.Line }
func (s *UniFactWithIffStmt) GetLine() uint              { return s.Line }
func (s *ClaimProveByContradictionStmt) GetLine() uint   { return s.Line }
func (s *EnumStmt) GetLine() uint                        { return s.Line }
func (s *IntensionalSetStmt) GetLine() uint              { return s.Line }
func (s *ClaimPropStmt) GetLine() uint                   { return s.Line }
func (s *ClaimExistPropStmt) GetLine() uint              { return s.Line }
func (s *ProveOverFiniteSetStmt) GetLine() uint          { return s.Line }
func (s *HaveObjInNonEmptySetStmt) GetLine() uint        { return s.Line }
func (s *HaveSetStmt) GetLine() uint                     { return s.Line }
func (s *HaveSetFnStmt) GetLine() uint                   { return s.Line }
func (s *HaveSetDefinedByReplacementStmt) GetLine() uint { return s.Line }
func (s *NamedUniFactStmt) GetLine() uint                { return s.Line }
func (s *EqualsFactStmt) GetLine() uint                  { return s.Line }
func (s *KnowExistPropStmt) GetLine() uint               { return s.Line }
func (s *CommentStmt) GetLine() uint                     { return s.Line }
func (s *FnTemplateDefStmt) GetLine() uint               { return s.Line }
func (s *ClearStmt) GetLine() uint                       { return s.Line }
func (s *InlineFactsStmt) GetLine() uint                 { return s.Line }
func (s *ProveByInductionStmt) GetLine() uint            { return s.Line }
func (s *HaveObjEqualStmt) GetLine() uint                { return s.Line }
func (s *HaveFnEqualStmt) GetLine() uint                 { return s.Line }
func (s *HaveFnLiftStmt) GetLine() uint                  { return s.Line }
func (s *HaveFnStmt) GetLine() uint                      { return s.Line }

type FactStmt interface {
	factStmt()
	stmt()
	String() string
	Instantiate(map[string]Fc) (FactStmt, error)
	GetAtoms() []FcAtom
	ToLatexString() string
	canBeKnown()
	InlineString() string
	ReplaceFc(oldFc Fc, newFc Fc) FactStmt
	GetLine() uint
}

func (p *SpecFactStmt) factStmt()       {}
func (l *UniFactStmt) factStmt()        {}
func (l *UniFactWithIffStmt) factStmt() {}
func (s *OrStmt) factStmt()             {}
func (s *EnumStmt) factStmt()           {}
func (s *IntensionalSetStmt) factStmt() {}
func (s *EqualsFactStmt) factStmt()     {}

type Spec_OrFact interface {
	reversibleFact()
	factStmt()
	stmt()
	String() string
	Instantiate(uniConMap map[string]Fc) (FactStmt, error)
	ReverseIsTrue() []*SpecFactStmt
	GetAtoms() []FcAtom
	ToLatexString() string
	canBeKnown()
	InlineString() string
	ReplaceFc(oldFc Fc, newFc Fc) FactStmt
	GetLine() uint
}

func (s *SpecFactStmt) reversibleFact() {}
func (s *OrStmt) reversibleFact()       {}

func (stmt *SpecFactStmt) ReverseIsTrue() []*SpecFactStmt {
	return []*SpecFactStmt{stmt.ReverseTrue()}
}

func (stmt *OrStmt) ReverseIsTrue() []*SpecFactStmt {
	reversedFacts := make([]*SpecFactStmt, len(stmt.Facts))
	for i, fact := range stmt.Facts {
		reversedFacts[i] = fact.ReverseTrue()
	}
	return reversedFacts
}

type DefStmtInterface interface {
	defStmt()
	stmt()
	String() string
	ToLatexString() string
	InlineString() string
}

func (s *DefObjStmt) defStmt()       {}
func (s *DefPropStmt) defStmt()      {}
func (s *DefExistPropStmt) defStmt() {}
func (s *DefFnStmt) defStmt()        {}

type UniFactInterface interface {
	factStmt()
	stmt()
	String() string
	Instantiate(map[string]Fc) (FactStmt, error)
	GetAtoms() []FcAtom
	uniFact()
	ToLatexString() string
	canBeKnown()
	InlineString() string
	ReplaceFc(oldFc Fc, newFc Fc) FactStmt
	GetLine() uint
}

func (stmt *UniFactStmt) uniFact()        {}
func (stmt *UniFactWithIffStmt) uniFact() {}

type ClaimInterface interface {
	claimStmt()
	String() string
	stmt()
	ToLatexString() string
	InlineString() string
	GetLine() uint
}

func (stmt *ClaimProveStmt) claimStmt()                {}
func (stmt *ClaimProveByContradictionStmt) claimStmt() {}
func (stmt *ClaimPropStmt) claimStmt()                 {}
func (stmt *ClaimExistPropStmt) claimStmt()            {}

type ImportStmtInterface interface {
	importStmt()
	stmt()
	String() string
	ToLatexString() string
	InlineString() string
	GetLine() uint
}

func (stmt *ImportDirStmt) importStmt()  {}
func (stmt *ImportFileStmt) importStmt() {}

type EnumSet_IntensionalSet_EqualDom interface {
	setDeclarationStmt()
	String() string
	GetPropName() Fc
	factStmt()
	stmt()
	Instantiate(map[string]Fc) (FactStmt, error)
	GetAtoms() []FcAtom
	ToLatexString() string
	canBeKnown()
	InlineString() string
	ReplaceFc(oldFc Fc, newFc Fc) FactStmt
	GetLine() uint
}

func (stmt *EnumStmt) setDeclarationStmt()           {}
func (stmt *IntensionalSetStmt) setDeclarationStmt() {}
func (stmt *EnumStmt) GetPropName() Fc               { return stmt.CurSet }
func (stmt *IntensionalSetStmt) GetPropName() Fc     { return stmt.CurSet }

type FnTemplate_Or_DefObjStmtInterface interface {
	fnTemplate_Or_DefObjStmt()
	ToLatexString() string
	InlineString() string
}

func (stmt *DefObjStmt) fnTemplate_Or_DefObjStmt() {}

type CanBeKnownStmt interface {
	stmt()
	String() string
	ToLatexString() string
	canBeKnown()
	InlineString() string
	GetLine() uint
}

func (s *SpecFactStmt) canBeKnown()       {}
func (s *UniFactStmt) canBeKnown()        {}
func (s *UniFactWithIffStmt) canBeKnown() {}
func (s *OrStmt) canBeKnown()             {}
func (s *EnumStmt) canBeKnown()           {}
func (s *IntensionalSetStmt) canBeKnown() {}
func (s *EqualsFactStmt) canBeKnown()     {}
func (s *KnowPropStmt) canBeKnown()       {}

type CanBeKnownStmtSlice []CanBeKnownStmt

func (s FactStmtSlice) ToCanBeKnownStmtSlice() CanBeKnownStmtSlice {
	ret := make(CanBeKnownStmtSlice, len(s))
	for i, fact := range s {
		ret[i] = fact
	}
	return ret
}
