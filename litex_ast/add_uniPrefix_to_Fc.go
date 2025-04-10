package litex_ast

import (
	"fmt"
	glob "golitex/litex_global"
	"strings"
)

func FcAtomInUniParams(atom *FcAtom, uniParams map[string]int) (int, bool) {
	if atom.PkgName == "" {
		if prefixNum, ok := uniParams[atom.Value]; ok {
			return prefixNum, true
		}
	}
	return 0, false
}

func AddUniPrefixToFcAtom(atom *FcAtom, uniParams map[string]int) *FcAtom {
	if prefixNum, ok := FcAtomInUniParams(atom, uniParams); ok {
		atom.Value = strings.Repeat(glob.UniParamPrefix, prefixNum) + atom.Value
	}
	return atom
}

func AddUniPrefixToFc(fc Fc, uniParams map[string]int) (Fc, error) {
	fcAsAtom, ok := fc.(*FcAtom)
	if ok {
		return AddUniPrefixToFcAtom(fcAsAtom, uniParams), nil
	}

	fcAsFcFn, ok := fc.(*FcFn)
	if !ok {
		return nil, fmt.Errorf("invalid fc %s", fc.String())
	}

	newFcFn := FcFn{FcAtom{}, []*FcFnSeg{}}
	fcAsFcFn.FnHead = *AddUniPrefixToFcAtom(&fcAsFcFn.FnHead, uniParams)
	// if FcAtomInUniParams(&fcAsFcFn.FnHead, uniParams) {
	// 	return NewFcAtom("", glob.UniParamPrefix+fcAsFcFn.FnHead.Value), nil
	// } else {
	// 	newFcFn.FnHead = fcAsFcFn.FnHead
	// }

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

// func AddUniPrefixToFc2(fc Fc, uniParams map[string]int) (Fc, error) {
// 	fcAsAtom, ok := fc.(*FcAtom)
// 	if ok {
// 		return AddUniPrefixToFcAtom(fcAsAtom, uniParams), nil
// 	}

// 	fcAsFcFn, ok := fc.(*FcFn)
// 	if !ok {
// 		return nil, fmt.Errorf("invalid fc %s", fc.String())
// 	}

// 	newFcFn := FcFn{FcAtom{}, []*FcFnSeg{}}
// 	if FcAtomInUniParams(&fcAsFcFn.FnHead, uniParams) {
// 		return NewFcAtom("", glob.UniParamPrefix+fcAsFcFn.FnHead.Value), nil
// 	} else {
// 		newFcFn.FnHead = fcAsFcFn.FnHead
// 	}

// 	for _, seg := range fcAsFcFn.ParamSegs {
// 		curSeg := &FcFnSeg{[]Fc{}}
// 		newFcFn.ParamSegs = append(newFcFn.ParamSegs, curSeg)
// 		for _, param := range seg.Params {
// 			newFc, err := AddUniPrefixToFc(param, uniParams)
// 			if err != nil {
// 				return nil, fmt.Errorf("invalid fc %s", newFc.String())
// 			}
// 			curSeg.Params = append(curSeg.Params, newFc)
// 		}
// 	}

// 	return &newFcFn, nil
// }

// func FcAtomInUniParams2(atom *FcAtom, uniParams map[string]int) bool {
// 	if atom.PkgName == "" {
// 		_, ok := uniParams[atom.Value]
// 		return ok
// 	}
// 	return false
// }

// func AddUniPrefixToFcAtom2(atom *FcAtom, uniParams map[string]int) *FcAtom {
// 	if FcAtomInUniParams2(atom, uniParams) {
// 		atom.Value = fmt.Sprintf("%s%s", glob.UniParamPrefix, atom.Value)
// 	}
// 	return atom
// }
