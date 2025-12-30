package litex_ast

import (
	"fmt"
	"strconv"
)

type ExistStFactWithFreeParams struct {
	FactType               SpecFactType
	PropName               Atom
	ExistFreeParams        []string
	ExistFreeParamSets     []Obj
	ExistFreeParamsEqualTo []Obj
	Params                 []Obj
	Line                   uint
}

func (e *ExistStFactWithFreeParams) ToExistStFact() *SpecFactStmt {
	params := []Obj{}
	params = append(params, Atom(fmt.Sprintf("%d", len(e.ExistFreeParams))))
	for i := range e.ExistFreeParamSets {
		params = append(params, Atom(e.ExistFreeParams[i]))
		params = append(params, e.ExistFreeParamSets[i])
		params = append(params, e.ExistFreeParamsEqualTo[i])
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
	existFreeParamsEqualTo := []Obj{}
	for i := 1; i <= lenOfExistFreeParams*3; i++ {
		existFreeParams = append(existFreeParams, string(f.Params[i].(Atom)))
		i++
		existFreeParamSets = append(existFreeParamSets, f.Params[i+lenOfExistFreeParams])
		i++
		existFreeParamsEqualTo = append(existFreeParamsEqualTo, f.Params[i+lenOfExistFreeParams*2])
	}

	params := []Obj{}
	for i := lenOfExistFreeParams*3 + 1; i < len(f.Params); i++ {
		params = append(params, f.Params[i])
	}

	return NewExistStFactWithFreeParams(ft, propName, existFreeParams, existFreeParamSets, existFreeParamsEqualTo, params, f.Line)
}

func NewExistStFactWithFreeParams(factType SpecFactType, propName Atom, existFreeParams []string, existFreeParamSets []Obj, existFreeParamsEqualTo []Obj, params []Obj, line uint) *ExistStFactWithFreeParams {
	return &ExistStFactWithFreeParams{
		FactType:               factType,
		PropName:               propName,
		ExistFreeParams:        existFreeParams,
		ExistFreeParamSets:     existFreeParamSets,
		ExistFreeParamsEqualTo: existFreeParamsEqualTo,
		Params:                 params,
		Line:                   line,
	}
}
