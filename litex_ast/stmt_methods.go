package litex_ast

import (
	"fmt"
	glob "golitex/litex_global"
)

// func (stmt *SpecFactStmt) AddUniPrefix(uniParams []string) (*SpecFactStmt, error) {
// 	panic(":")
// }

// func addUniPrefixToFc(fc Fc, uniParams []string) (Fc, error) {
// 	fcAsAtom, ok := fc.(*FcAtom)
// 	if ok {
// 		if fcAsAtom.PkgName == "" {
// 			if strInStrSlice(fcAsAtom.Value, uniParams) {
// 				return NewFcAtom("", glob.UniFactParamPrefix+fcAsAtom.Value), nil
// 			}
// 		}
// 		return fc, nil
// 	}

// 	fcAsFcFn, ok := fc.(*FcFn)
// 	if !ok {
// 		return nil, fmt.Errorf("invalid fc %s", fc.String())
// 	}

// 	newFcFn := FcFn{FcAtom{}, []*FcFnSeg{}}
// 	if fcAsFcFn.FnHead.PkgName == "" {
// 		if strInStrSlice(fcAsFcFn.FnHead.Value, uniParams) {
// 			return NewFcAtom("", glob.UniFactParamPrefix+fcAsFcFn.FnHead.Value), nil
// 		}
// 	} else {
// 		newFcFn.FnHead = fcAsFcFn.FnHead
// 	}

// 	for _, seg := range fcAsFcFn.CallPipe {
// 		curSeg := &FcFnSeg{[]Fc{}}
// 		newFcFn.CallPipe = append(newFcFn.CallPipe, curSeg)
// 		for _, param := range seg.Params {
// 			newFc, err := addUniPrefixToFc(param, uniParams)
// 			if err != nil {
// 				return nil, fmt.Errorf("invalid fc %s", newFc.String())
// 			}
// 			curSeg.Params = append(curSeg.Params, newFc)
// 		}
// 	}

// 	return &newFcFn, nil
// }

// func strInStrSlice(str string, strSlice []string) bool {
// 	for _, uniParam := range strSlice {
// 		if uniParam == str {
// 			return true
// 		}
// 	}
// 	return false
// }

func (stmt *SpecFactStmt) AddUniPrefix(uniParams map[string]struct{}) (*SpecFactStmt, error) {
	panic("")
}

func addUniPrefixToFc(fc Fc, uniParams map[string]struct{}) (Fc, error) {
	fcAsAtom, ok := fc.(*FcAtom)
	if ok {
		if fcAsAtom.PkgName == "" {
			if _, exists := uniParams[fcAsAtom.Value]; exists {
				return NewFcAtom("", glob.UniFactParamPrefix+fcAsAtom.Value), nil
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
		if _, exists := uniParams[fcAsFcFn.FnHead.Value]; exists {
			return NewFcAtom("", glob.UniFactParamPrefix+fcAsFcFn.FnHead.Value), nil
		}
	} else {
		newFcFn.FnHead = fcAsFcFn.FnHead
	}

	for _, seg := range fcAsFcFn.CallPipe {
		curSeg := &FcFnSeg{[]Fc{}}
		newFcFn.CallPipe = append(newFcFn.CallPipe, curSeg)
		for _, param := range seg.Params {
			newFc, err := addUniPrefixToFc(param, uniParams)
			if err != nil {
				return nil, fmt.Errorf("invalid fc %s", newFc.String())
			}
			curSeg.Params = append(curSeg.Params, newFc)
		}
	}

	return &newFcFn, nil
}
