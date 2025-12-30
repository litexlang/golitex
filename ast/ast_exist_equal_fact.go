package litex_ast

import (
	"fmt"
	"strconv"
)

type ExistStFactWithEqualityStruct struct {
	FactType           SpecFactType
	PropName           Atom
	ExistFreeParams    []string
	ExistFreeParamSets []Obj
	EqualTos           []Obj
	Params             []Obj
	Line               uint
}

func NewExistStFactWithEqualityStruct(factType SpecFactType, propName Atom, existFreeParams []string, existFreeParamSets []Obj, equalTos []Obj, params []Obj, line uint) *ExistStFactWithEqualityStruct {
	return &ExistStFactWithEqualityStruct{
		FactType:           factType,
		PropName:           propName,
		ExistFreeParams:    existFreeParams,
		ExistFreeParamSets: existFreeParamSets,
		EqualTos:           equalTos,
		Params:             params,
		Line:               line,
	}
}

func NewExistStFactWithEquality(factType SpecFactType, propName Atom, existFreeParams []string, existFreeParamSets []Obj, equalTos []Obj, params []Obj, line uint) *SpecFactStmt {
	s := NewExistStFactWithEqualityStruct(factType, propName, existFreeParams, existFreeParamSets, equalTos, params, line)
	return s.ToExistStFact()
}

func (e *ExistStFactWithEqualityStruct) ToExistStFact() *SpecFactStmt {
	params := []Obj{}
	params = append(params, Atom(fmt.Sprintf("%d", len(e.ExistFreeParams))))
	for i := range e.ExistFreeParamSets {
		params = append(params, Atom(e.ExistFreeParams[i]))
		params = append(params, e.ExistFreeParamSets[i])
		params = append(params, e.EqualTos[i])
	}

	for i := range e.Params {
		params = append(params, e.Params[i])
	}

	return NewSpecFactStmt(e.FactType, e.PropName, params, e.Line)
}

func (f *SpecFactStmt) ToExistStFactWithEqualityStruct() *ExistStFactWithEqualityStruct {
	ft := f.FactType
	propName := f.PropName
	lenOfExistFreeParams, _ := strconv.Atoi(string(f.Params[0].(Atom))) // 第一param变成string然后变成int
	existFreeParams := []string{}
	existFreeParamSets := []Obj{}
	equalTos := []Obj{}

	for i := 1; i <= lenOfExistFreeParams*3; i++ {
		existFreeParams = append(existFreeParams, string(f.Params[i].(Atom)))
		i++
		existFreeParamSets = append(existFreeParamSets, f.Params[i+lenOfExistFreeParams])
		i++
		equalTos = append(equalTos, f.Params[i+lenOfExistFreeParams*2])
	}

	params := []Obj{}
	for i := lenOfExistFreeParams*3 + 1; i < len(f.Params); i++ {
		params = append(params, f.Params[i])
	}

	return NewExistStFactWithEqualityStruct(ft, propName, existFreeParams, existFreeParamSets, equalTos, params, f.Line)
}
