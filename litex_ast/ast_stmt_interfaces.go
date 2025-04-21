// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen (malloc_realloc_calloc@outlook.com)
// Visit litexlang.org and https://github.com/litexlang/golitex for more information.

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
func (f *ClaimProveStmt) stmt()   {}
func (f *KnowStmt) stmt()         {}

func (s *DefConExistPropStmt) stmt() {}
func (s *HaveStmt) stmt()            {}
func (s *AxiomStmt) stmt()           {}
func (s *ThmStmt) stmt()             {}
func (s *CondFactStmt) stmt()        {}
func (s *GenUniStmt) stmt()          {}
func (p *OrAndFact) stmt()           {}

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
func (p *OrAndFact) factStmt()      {}

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

// func (s *ExistFactStmt) propFactStmt() {}
