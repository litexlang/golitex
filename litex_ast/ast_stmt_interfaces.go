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

func (stmt *DefObjStmt) stmt()    {}
func (c *DefInterfaceStmt) stmt() {}
func (f *DefTypeStmt) stmt()      {}
func (c *DefConPropStmt) stmt()   {}
func (f *DefConFnStmt) stmt()     {}
func (l *ConUniFactStmt) stmt()   {}
func (p *SpecFactStmt) stmt()     {}
func (f *ClaimStmt) stmt()        {}
func (f *KnowStmt) stmt()         {}

func (s *DefConExistPropStmt) stmt()  {}
func (s *AxiomStmt) stmt()            {}
func (s *ThmStmt) stmt()              {}
func (s *CondFactStmt) stmt()         {}
func (s *GenUniStmt) stmt()           {}
func (p *LogicExprStmt) stmt()        {}
func (s *ExistObjDefStmt) stmt()      {}
func (s *SetDefSetBuilderStmt) stmt() {}
func (s *SetDefEnumtmt) stmt()        {}

// func (s *ExistFactStmt) stmt() {}

type FactStmt interface {
	factStmt()
	stmt()
	String() string
	Instantiate(map[string]Fc) (FactStmt, error)
}

func (p *SpecFactStmt) factStmt()   {}
func (p *CondFactStmt) factStmt()   {}
func (l *ConUniFactStmt) factStmt() {}
func (p *GenUniStmt) factStmt()     {}
func (p *LogicExprStmt) factStmt()  {}

// func (p *ExistFactStmt) factStmt()  {}

type SpecFactParams struct {
	ObjParams []Fc
}

type DefPropOrExistPropStmt interface {
	defPropStmt()
	stmt()
}

func (s *DefConExistPropStmt) defPropStmt() {}
func (s *DefConPropStmt) defPropStmt()      {}

type DefMember interface {
	defMember()
}

func (s *DefObjStmt) defMember()     {}
func (s *DefConFnStmt) defMember()   {}
func (s *DefConPropStmt) defMember() {}

func (s *DefConExistPropStmt) defMember() {}

type UniFactStmt interface {
	factStmt()
	stmt()
	String() string
	forallStmt()
	Instantiate(map[string]Fc) (FactStmt, error)
}

func (s *ConUniFactStmt) forallStmt() {}
func (s *GenUniStmt) forallStmt()     {}

type PropFactStmt interface {
	factStmt()
	stmt()
	String() string
	Instantiate(map[string]Fc) (FactStmt, error)
	propFactStmt()
}

func (s *SpecFactStmt) propFactStmt() {}

type SetDefStmt interface {
	setDefStmt()
	stmt()
	String() string
}

func (s *SetDefSetBuilderStmt) setDefStmt() {}
func (s *SetDefEnumtmt) setDefStmt()        {}

type LogicExprOrSpecFactStmt interface {
	logicExprOrSpecFactStmt()
	factStmt()
	stmt()
	String() string
	Instantiate(uniConMap map[string]Fc) (FactStmt, error)
	Reverse() LogicExprOrSpecFactStmt
}

func (s *LogicExprStmt) logicExprOrSpecFactStmt() {}
func (s *SpecFactStmt) logicExprOrSpecFactStmt()  {}

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

type DefStmt interface {
	defStmt()
	stmt()
	String() string
}

func (s *DefObjStmt) defStmt()          {}
func (s *DefConFnStmt) defStmt()        {}
func (s *DefConPropStmt) defStmt()      {}
func (s *DefConExistPropStmt) defStmt() {}
