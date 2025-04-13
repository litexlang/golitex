package litex_ast

import (
	"fmt"
	glob "golitex/litex_global"
	"strings"
)

type NameDepthMap map[string]int

func AddUniPrefixToFcAtom(atom *FcAtom, uniParams NameDepthMap) *FcAtom {
	if prefixNum, ok := fcAtomInUniParams(atom, uniParams); ok {
		atom.Value = strings.Repeat(glob.UniParamPrefix, prefixNum) + atom.Value
	}
	return atom
}

func AddUniPrefixToFc(fc Fc, uniParams NameDepthMap) (Fc, error) {
	fcAsAtom, ok := fc.(*FcAtom)
	if ok {
		return AddUniPrefixToFcAtom(fcAsAtom, uniParams), nil
	}

	fcAsFcFn, ok := fc.(*FcFn)
	if !ok {
		return nil, fmt.Errorf("invalid fc %s", fc.String())
	}

	newFcFn := FcFn{FcAtom{}, []*FcFnSeg{}}
	newFcFn.FnHead = *AddUniPrefixToFcAtom(&fcAsFcFn.FnHead, uniParams)

	for _, seg := range fcAsFcFn.ParamSegs {
		curSeg := &FcFnSeg{[]Fc{}}
		newFcFn.ParamSegs = append(newFcFn.ParamSegs, curSeg)
		for _, param := range seg.Params {
			newFc, err := AddUniPrefixToFc(param, uniParams)
			if err != nil {
				return nil, err
			}
			curSeg.Params = append(curSeg.Params, newFc)
		}
	}

	return &newFcFn, nil
}

func fcAtomInUniParams(atom *FcAtom, uniParams NameDepthMap) (int, bool) {
	if atom.PkgName == "" {
		if prefixNum, ok := uniParams[atom.Value]; ok {
			return prefixNum, true
		}
	}
	return 0, false
}
