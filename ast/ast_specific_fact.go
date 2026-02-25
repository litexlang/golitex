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
	Key() Atom
	GetFactType() SpecFactType
}

func (s *PureSpecificFactStmt) reversibleFact()  {}
func (s *ExistSpecificFactStmt) reversibleFact() {}

func (s *PureSpecificFactStmt) specificFactStmt()  {}
func (s *ExistSpecificFactStmt) specificFactStmt() {}

func (s *PureSpecificFactStmt) Key() Atom {
	return s.PropName
}

func (s *ExistSpecificFactStmt) Key() Atom {
	ret := ""
	for i, pureFact := range s.PureFacts {
		ret += pureFact.PropName.String()
		if i != len(s.PureFacts)-1 {
			ret += ","
		}
	}
	return Atom(ret)
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
	ExistFreeParamSets ObjSlice
	PureFacts          []*PureSpecificFactStmt
	Line               uint
}

func (s *PureSpecificFactStmt) ReverseIsTrue() []SpecificFactStmt {
	return []SpecificFactStmt{NewPureSpecificFactStmt(!s.IsTrue, s.PropName, s.Params, s.Line)}
}

func (s *ExistSpecificFactStmt) ReverseIsTrue() []SpecificFactStmt {
	return []SpecificFactStmt{NewExistSpecificFactStmt(!s.IsTrue, s.ExistFreeParams, s.ExistFreeParamSets, s.PureFacts, s.GetLine())}
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

func NewParamSetsWhenParamIsChanged(originalParam []string, paramSet []Obj, newParam []string) ([]Obj, error) {
	uniMap := map[string]Obj{}
	newParamSets := make([]Obj, len(paramSet))

	for i := range originalParam {
		cur, err := paramSet[i].Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newParamSets[i] = cur
		uniMap[originalParam[i]] = Atom(newParam[i])
	}

	return newParamSets, nil
}

func (e *ExistSpecificFactStmt) ReplaceFreeParamsWithNewParams(newExistFreeParams []string) (*ExistSpecificFactStmt, error) {
	newParamSets, err := NewParamSetsWhenParamIsChanged(e.ExistFreeParams, e.ExistFreeParamSets, newExistFreeParams)
	if err != nil {
		return nil, err
	}

	uniMap := map[string]Obj{}
	for i := range newExistFreeParams {
		uniMap[e.ExistFreeParams[i]] = Atom(newExistFreeParams[i])
	}

	newPureFact := make([]*PureSpecificFactStmt, len(e.PureFacts))
	for i, pureFact := range e.PureFacts {
		tmp, err := pureFact.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newPureFact[i] = tmp.(*PureSpecificFactStmt)
	}

	return NewExistSpecificFactStmt(e.IsTrue, newExistFreeParams, newParamSets, newPureFact, e.Line), nil
}
