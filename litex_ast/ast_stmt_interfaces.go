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

func (stmt *DefObjStmt) stmt()  {}
func (c *DefConPropStmt) stmt() {}
func (f *DefConFnStmt) stmt()   {}
func (l *UniFactStmt) stmt()    {}
func (p *SpecFactStmt) stmt()   {}
func (f *ClaimStmt) stmt()      {}
func (f *KnowStmt) stmt()       {}

func (s *DefConExistPropStmt) stmt() {}

func (s *AxiomStmt) stmt() {}

// func (s *ThmStmt) stmt()             {}

// func (s *CondFactStmt) stmt()         {}
func (p *LogicExprStmt) stmt()        {}
func (s *ExistObjDefStmt) stmt()      {}
func (s *SetDefSetBuilderStmt) stmt() {}
func (s *SetDefEnumtmt) stmt()        {}
func (s *MatcherEnvStmt) stmt()       {}

type FactStmt interface {
	factStmt()
	stmt()
	String() string
	Instantiate(map[string]Fc) (FactStmt, error)
}

func (p *SpecFactStmt) factStmt()  {}
func (l *UniFactStmt) factStmt()   {}
func (p *LogicExprStmt) factStmt() {}

// func (p *CondFactStmt) factStmt()   {}

type SpecFactParams struct {
	ObjParams []Fc
}

// type DefPropOrExistPropStmt interface {
// 	defStmt()
// 	defPropStmt()
// 	stmt()
// 	String() string
// 	UniFactWhereDomImplyPropFact() (*UniFactStmt, error)
// }

// func (s *DefConExistPropStmt) defPropStmt() {}
// func (s *DefConPropStmt) defPropStmt()      {}

type SetDefStmt interface {
	setDefStmt()
	stmt()
	String() string
	Name() string
}

func (s *SetDefSetBuilderStmt) setDefStmt() {}
func (s *SetDefEnumtmt) setDefStmt()        {}
func (s *SetDefSetBuilderStmt) Name() string {
	return s.SetName
}
func (s *SetDefEnumtmt) Name() string {
	return s.SetName
}

type LogicExprOrSpecFactStmt interface {
	logicExprOrSpecFactStmt()
	factStmt()
	stmt()
	String() string
	Instantiate(uniConMap map[string]Fc) (FactStmt, error)
	Reverse() LogicExprOrSpecFactStmt
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

func (s *LogicExprStmt) Reverse() LogicExprOrSpecFactStmt {
	newFacts := make([]LogicExprOrSpecFactStmt, len(s.Facts))
	for i, fact := range s.Facts {
		newFacts[i] = fact.Reverse()
	}
	return &LogicExprStmt{
		IsOr:  !s.IsOr,
		Facts: newFacts,
	}
}

func (s *SpecFactStmt) Reverse() LogicExprOrSpecFactStmt {
	return s.ReverseIsTrue()
}

// 用于处理 forall x Type. 这里的 Type 可以是 obj, fn, prop, existProp.
type DefStmt interface {
	defStmt()
	stmt()
	String() string
}

func (s *DefObjStmt) defStmt()          {}
func (s *DefConFnStmt) defStmt()        {}
func (s *DefConPropStmt) defStmt()      {}
func (s *DefConExistPropStmt) defStmt() {}
