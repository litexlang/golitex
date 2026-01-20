// Copyright Jiachen Shen.
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

type SpecificFactStmt interface {
	reversibleFact()
	specificFactStmt()
	factStmt()
	stmt()
	String() string
	InstantiateFact(map[string]Obj) (FactStmt, error)
	ToLatexString() string
	canBeKnown()
	InlineString() string
	GetLine() uint
	algoStmt()
	Instantiate(map[string]Obj) (Stmt, error)
	SetLine(l uint)
	ReverseIsTrue() []SpecificFactStmt
	GetPropName() Atom
	GetFactType() SpecFactType
}

func (s *PureSpecificFactStmt) reversibleFact()  {}
func (s *ExistSpecificFactStmt) reversibleFact() {}

func (s *PureSpecificFactStmt) specificFactStmt()  {}
func (s *ExistSpecificFactStmt) specificFactStmt() {}

func (s *PureSpecificFactStmt) GetPropName() Atom {
	return s.PropName
}

func (s *ExistSpecificFactStmt) GetPropName() Atom {
	return s.PureFact.PropName
}

type PureSpecificFactStmt struct {
	IsTrue   bool
	PropName Atom
	Params   ObjSlice
	Line     uint
}

type ExistSpecificFactStmt struct {
	IsTrue             bool
	ExistFreeParams    []string
	ExistFreeParamSets []Obj
	PureFact           *PureSpecificFactStmt
	Line               uint
}

func (s *PureSpecificFactStmt) ReverseIsTrue() []SpecificFactStmt {
	return []SpecificFactStmt{NewPureSpecificFactStmt(!s.IsTrue, s.PropName, s.Params, s.Line)}
}

func (s *ExistSpecificFactStmt) ReverseIsTrue() []SpecificFactStmt {
	return []SpecificFactStmt{NewExistSpecificFactStmt(!s.IsTrue, s.ExistFreeParams, s.ExistFreeParamSets, s.PureFact, s.Line)}
}

func (s *PureSpecificFactStmt) GetFactType() SpecFactType {
	if s.IsTrue {
		return TruePure
	} else {
		return FalsePure
	}
}

func (s *ExistSpecificFactStmt) GetFactType() SpecFactType {
	if s.IsTrue {
		return TrueExist_St
	} else {
		return FalseExist_St
	}
}
