package litex_ast

import (
	"fmt"
	glob "golitex/litex_global"
)

func FcAtomInUniParams(atom *FcAtom, uniParams map[string]struct{}) bool {
	if atom.PkgName == "" {
		if _, ok := uniParams[atom.Value]; ok {
			return true
		}
	}
	return false
}

func AddUniPrefixToFcAtom(atom *FcAtom, uniParams map[string]struct{}) *FcAtom {
	if FcAtomInUniParams(atom, uniParams) {
		atom.Value = fmt.Sprintf("%s%s", glob.UniParamPrefix, atom.Value)
	}
	return atom
}

func AddUniPrefixToFc(fc Fc, uniParams map[string]struct{}) (Fc, error) {
	fcAsAtom, ok := fc.(*FcAtom)
	if ok {
		return AddUniPrefixToFcAtom(fcAsAtom, uniParams), nil
	}

	fcAsFcFn, ok := fc.(*FcFn)
	if !ok {
		return nil, fmt.Errorf("invalid fc %s", fc.String())
	}

	newFcFn := FcFn{FcAtom{}, []*FcFnSeg{}}
	if FcAtomInUniParams(&fcAsFcFn.FnHead, uniParams) {
		return NewFcAtom("", glob.UniParamPrefix+fcAsFcFn.FnHead.Value), nil
	} else {
		newFcFn.FnHead = fcAsFcFn.FnHead
	}

	for _, seg := range fcAsFcFn.ParamSegs {
		curSeg := &FcFnSeg{[]Fc{}}
		newFcFn.ParamSegs = append(newFcFn.ParamSegs, curSeg)
		for _, param := range seg.Params {
			newFc, err := AddUniPrefixToFc(param, uniParams)
			if err != nil {
				return nil, fmt.Errorf("invalid fc %s", newFc.String())
			}
			curSeg.Params = append(curSeg.Params, newFc)
		}
	}

	return &newFcFn, nil
}
