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
// Litex Zulip community: https://litex.zulipchat.com

package litex_ast

type Stmt interface {
	stmt()
	String() string
}

func (stmt *DefObjStmt) stmt()                 {}
func (c *DefPropStmt) stmt()                   {}
func (f *DefFnStmt) stmt()                     {}
func (l *UniFactStmt) stmt()                   {}
func (p *SpecFactStmt) stmt()                  {}
func (f *ClaimProveStmt) stmt()                {}
func (f *KnowFactStmt) stmt()                  {}
func (s *DefExistPropStmt) stmt()              {}
func (s *HaveStmt) stmt()                      {}
func (s *SupposeStmt) stmt()                   {}
func (s *WithStmt) stmt()                      {}
func (s *ProveInEachCaseStmt) stmt()           {}
func (s *KnowPropStmt) stmt()                  {}
func (s *KnowExistPropStmt) stmt()             {}
func (s *OrStmt) stmt()                        {}
func (s *ImportStmt) stmt()                    {}
func (s *PubStmt) stmt()                       {}
func (s *ProveStmt) stmt()                     {}
func (s *UniFactWithIffStmt) stmt()            {}
func (s *ClaimProveByContradictionStmt) stmt() {}

type FactStmt interface {
	factStmt()
	stmt()
	String() string
	Instantiate(map[string]Fc) (FactStmt, error)
	GetAtoms() []*FcAtom
}

func (p *SpecFactStmt) factStmt()       {}
func (l *UniFactStmt) factStmt()        {}
func (l *UniFactWithIffStmt) factStmt() {}
func (s *OrStmt) factStmt()             {}

type SpecFactParams struct {
	ObjParams []Fc
}

type OrStmt_SpecStmt interface {
	logicExprOrSpecFactStmt()
	factStmt()
	stmt()
	String() string
	Instantiate(uniConMap map[string]Fc) (FactStmt, error)
	ReverseIsTrue() []SpecFactStmt
	GetAtoms() []*FcAtom
}

func (s *SpecFactStmt) logicExprOrSpecFactStmt() {}
func (s *OrStmt) logicExprOrSpecFactStmt()       {}

func (stmt *SpecFactStmt) ReverseIsTrue() []SpecFactStmt {
	return []SpecFactStmt{*stmt.ReverseTrue()}
}

func (stmt *OrStmt) ReverseIsTrue() []SpecFactStmt {
	reversedFacts := make([]SpecFactStmt, len(stmt.Facts))
	for i, fact := range stmt.Facts {
		reversedFacts[i] = *fact.ReverseTrue()
	}
	return reversedFacts
}

type DefStmt interface {
	defStmt()
	stmt()
	String() string
}

func (s *DefObjStmt) defStmt()       {}
func (s *DefFnStmt) defStmt()        {}
func (s *DefPropStmt) defStmt()      {}
func (s *DefExistPropStmt) defStmt() {}

type UniFactInterface interface {
	factStmt()
	stmt()
	String() string
	Instantiate(map[string]Fc) (FactStmt, error)
	GetAtoms() []*FcAtom
	uniFact()
}

func (stmt *UniFactStmt) uniFact()        {}
func (stmt *UniFactWithIffStmt) uniFact() {}

type ClaimInterface interface {
	claimStmt()
	String() string
	stmt()
}

func (stmt *ClaimProveStmt) claimStmt()                {}
func (stmt *ClaimProveByContradictionStmt) claimStmt() {}
