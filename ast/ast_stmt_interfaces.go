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

type Stmt interface {
	stmt()
	String() string
	ToLatexString() string
	InlineString() string
}

func (stmt *DefObjStmt) stmt()                   {}
func (c *DefPropStmt) stmt()                     {}
func (l *DefFnStmt) stmt()                       {}
func (l *UniFactStmt) stmt()                     {}
func (p *SpecFactStmt) stmt()                    {}
func (f *ClaimProveStmt) stmt()                  {}
func (f *KnowFactStmt) stmt()                    {}
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
func (s *ProveByMathInductionStmt) stmt()        {}
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

type FactStmt interface {
	factStmt()
	stmt()
	String() string
	Instantiate(map[string]Fc) (FactStmt, error)
	GetAtoms() []FcAtom
	ToLatexString() string
	canBeKnown()
	InlineString() string
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
}

func (stmt *UniFactStmt) uniFact()        {}
func (stmt *UniFactWithIffStmt) uniFact() {}

type ClaimInterface interface {
	claimStmt()
	String() string
	stmt()
	ToLatexString() string
	InlineString() string
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
