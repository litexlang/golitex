// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Contact the development team: <litexlang@outlook.com>
// Visit litexlang.org and https://github.com/litexlang/golitex for more info.

package litex_ast

type Stmt interface {
	stmt()
	String() string
}

func (stmt *DefObjStmt) stmt() {}
func (c *DefPropStmt) stmt()   {}
func (f *DefFnStmt) stmt()     {}
func (l *UniFactStmt) stmt()   {}
func (p *SpecFactStmt) stmt()  {}
func (f *ClaimStmt) stmt()     {}
func (f *KnowFactStmt) stmt()  {}

func (s *DefExistPropStmt) stmt() {}

// func (s *AxiomStmt) stmt() {}

// func (s *ThmStmt) stmt()             {}

// func (s *CondFactStmt) stmt()         {}
func (p *LogicExprStmt) stmt()        {}
func (s *HaveStmt) stmt()             {}
func (s *SetDefSetBuilderStmt) stmt() {}

// func (s *SetDefEnumtmt) stmt()        {}
func (s *MatcherEnvStmt) stmt() {}

func (s *ProveInEachCaseStmt) stmt() {}

func (s *KnowPropStmt) stmt()      {}
func (s *KnowExistPropStmt) stmt() {}
func (s *ProveOrStmt) stmt()       {}

type FactStmt interface {
	factStmt()
	stmt()
	String() string
	Instantiate(map[string]Fc) (FactStmt, error)
}

func (p *SpecFactStmt) factStmt()  {}
func (l *UniFactStmt) factStmt()   {}
func (p *LogicExprStmt) factStmt() {}

type SpecFactParams struct {
	ObjParams []Fc
}

type Reversable_LogicOrSpec_Stmt interface {
	logicExprOrSpecFactStmt()
	factStmt()
	stmt()
	String() string
	Instantiate(uniConMap map[string]Fc) (FactStmt, error)
	ReverseIsTrue() Reversable_LogicOrSpec_Stmt
	IsSpecFactNameWithUniPrefix() bool
}

func (s *LogicExprStmt) logicExprOrSpecFactStmt() {}
func (s *SpecFactStmt) logicExprOrSpecFactStmt()  {}
func (s *LogicExprStmt) IsSpecFactNameWithUniPrefix() bool {
	for _, fact := range s.Facts {
		if fact.IsSpecFactNameWithUniPrefix() {
			return true
		}
	}
	return false
}

func (s *LogicExprStmt) ReverseIsTrue() Reversable_LogicOrSpec_Stmt {
	newFacts := make([]Reversable_LogicOrSpec_Stmt, len(s.Facts))
	for i, fact := range s.Facts {
		newFacts[i] = fact.ReverseIsTrue()
	}
	return &LogicExprStmt{
		IsOr:  !s.IsOr,
		Facts: newFacts,
	}
}

func (stmt *SpecFactStmt) ReverseIsTrue() Reversable_LogicOrSpec_Stmt {
	return stmt.ReverseSpecFact()
}

// 用于处理 forall x Type. 这里的 Type 可以是 obj, fn, prop, existProp.
type DefStmt interface {
	defStmt()
	stmt()
	String() string
}

func (s *DefObjStmt) defStmt()       {}
func (s *DefFnStmt) defStmt()        {}
func (s *DefPropStmt) defStmt()      {}
func (s *DefExistPropStmt) defStmt() {}
