package litex_ast

import (
	"fmt"
	glob "golitex/glob"
)

type InstSetTemplateObj struct {
	Name   Atom
	Params ObjSlice
}

func (o *InstSetTemplateObj) Obj() {}
func (o *InstSetTemplateObj) String() string {
	return fmt.Sprintf("%s%s(%s)", glob.KeySymbolAt, o.Name, o.Params)
}

func NewInstSetTemplateObj(name Atom, params ObjSlice) *InstSetTemplateObj {
	return &InstSetTemplateObj{Name: name, Params: params}
}

func (obj *InstSetTemplateObj) Instantiate(uniMap map[string]Obj) (Obj, error) {
	instantiatedParams := make([]Obj, len(obj.Params))
	for i, param := range obj.Params {
		instantiatedParam, err := param.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		instantiatedParams[i] = instantiatedParam
	}
	return NewInstSetTemplateObj(obj.Name, instantiatedParams), nil
}

func (obj *InstSetTemplateObj) ToLatexString() string {
	return fmt.Sprintf("%s%s(%s)", glob.KeySymbolAt, obj.Name, obj.Params)
}
