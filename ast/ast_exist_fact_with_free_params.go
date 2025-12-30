package litex_ast

import (
	"fmt"
	"strconv"
)

type ExistStFactWithFreeParams struct {
	FactType           SpecFactType
	PropName           Atom
	ExistFreeParams    []string
	ExistFreeParamSets []Obj
	Params             []Obj
	Line               uint
}

type ExistStFactWithFreeParamsAndEquality struct {
	FactType           SpecFactType
	PropName           Atom
	ExistFreeParams    []string
	ExistFreeParamSets []Obj
	EqualTos           []Obj
	Params             []Obj
	Line               uint
}

func NewExistStFactWithFreeParams(factType SpecFactType, propName Atom, existFreeParams []string, existFreeParamSets []Obj, params []Obj, line uint) *ExistStFactWithFreeParams {
	return &ExistStFactWithFreeParams{
		FactType:           factType,
		PropName:           propName,
		ExistFreeParams:    existFreeParams,
		ExistFreeParamSets: existFreeParamSets,
		Params:             params,
		Line:               line,
	}
}

func NewExistStFactWithFreeParamsAndEquality(factType SpecFactType, propName Atom, existFreeParams []string, existFreeParamSets []Obj, equalTos []Obj, params []Obj, line uint) *ExistStFactWithFreeParamsAndEquality {
	return &ExistStFactWithFreeParamsAndEquality{
		FactType:           factType,
		PropName:           propName,
		ExistFreeParams:    existFreeParams,
		ExistFreeParamSets: existFreeParamSets,
		EqualTos:           equalTos,
		Params:             params,
		Line:               line,
	}
}

func (e *ExistStFactWithFreeParams) ToExistStFact() *SpecFactStmt {
	params := []Obj{}
	params = append(params, Atom(fmt.Sprintf("%d", len(e.ExistFreeParams))))
	for i := range e.ExistFreeParamSets {
		params = append(params, Atom(e.ExistFreeParams[i]))
		params = append(params, e.ExistFreeParamSets[i])
	}

	for i := range e.Params {
		params = append(params, e.Params[i])
	}

	return NewSpecFactStmt(e.FactType, e.PropName, params, e.Line)
}

func (e *ExistStFactWithFreeParamsAndEquality) ToExistStFact() *SpecFactStmt {
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

func (f *SpecFactStmt) ToExistStFactWithFreeParams() *ExistStFactWithFreeParams {
	ft := f.FactType
	propName := f.PropName
	lenOfExistFreeParams, _ := strconv.Atoi(string(f.Params[0].(Atom))) // 第一param变成string然后变成int
	existFreeParams := []string{}
	existFreeParamSets := []Obj{}
	for i := 1; i <= lenOfExistFreeParams*2; i++ {
		existFreeParams = append(existFreeParams, string(f.Params[i].(Atom)))
		i++
		existFreeParamSets = append(existFreeParamSets, f.Params[i+lenOfExistFreeParams])
		i++
	}

	params := []Obj{}
	for i := lenOfExistFreeParams*2 + 1; i < len(f.Params); i++ {
		params = append(params, f.Params[i])
	}

	return NewExistStFactWithFreeParams(ft, propName, existFreeParams, existFreeParamSets, params, f.Line)
}

func (f *SpecFactStmt) ToExistStFactWithFreeParamsAndEquality() *ExistStFactWithFreeParamsAndEquality {
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

	return NewExistStFactWithFreeParamsAndEquality(ft, propName, existFreeParams, existFreeParamSets, equalTos, params, f.Line)
}
