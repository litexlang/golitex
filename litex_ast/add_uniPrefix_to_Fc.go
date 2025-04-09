package litex_ast

import (
	"fmt"
	glob "golitex/litex_global"
)

func AddUniPrefixToFc(fc Fc, uniParams map[string]struct{}) (Fc, error) {
	fcAsAtom, ok := fc.(*FcAtom)
	if ok {
		if fcAsAtom.PkgName == "" {
			if _, exists := uniParams[glob.UniParamPrefix+fcAsAtom.Value]; exists {
				return NewFcAtom("", glob.UniParamPrefix+fcAsAtom.Value), nil
			}
		}
		return fc, nil
	}

	fcAsFcFn, ok := fc.(*FcFn)
	if !ok {
		return nil, fmt.Errorf("invalid fc %s", fc.String())
	}

	newFcFn := FcFn{FcAtom{}, []*FcFnSeg{}}
	if fcAsFcFn.FnHead.PkgName == "" {
		if _, exists := uniParams[glob.UniParamPrefix+fcAsFcFn.FnHead.Value]; exists {
			return NewFcAtom("", glob.UniParamPrefix+fcAsFcFn.FnHead.Value), nil
		}
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
