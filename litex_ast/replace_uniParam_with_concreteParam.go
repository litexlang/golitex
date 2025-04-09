package litex_ast

import "fmt"

func (fc *FcAtom) Instantiate(uniParamConParamMap map[string]Fc) (Fc, error) {
	if fc.PkgName == "" {
		instance, ok := uniParamConParamMap[fc.Value]
		if ok {
			return instance, nil
		}
	}
	return fc, nil
}

func (fc *FcFn) Instantiate(uniParamConParamMap map[string]Fc) (Fc, error) {
	newFc := FcFn{FcAtom{}, []*FcFnSeg{}}
	var err error = nil

	newHead, err := fc.FnHead.Instantiate(uniParamConParamMap)
	if err != nil {
		return nil, err
	}

	if newHeadAsAtom, ok := newHead.(*FcAtom); ok {
		newFc.FnHead = *newHeadAsAtom
	} else {
		newHeadAsFcFn, ok := newHead.(*FcFn)
		if !ok {
			return nil, fmt.Errorf("")
		}
		newFc.FnHead = newHeadAsFcFn.FnHead
		newFc.ParamSegs = append(newFc.ParamSegs, newHeadAsFcFn.ParamSegs...)
	}

	for _, seg := range fc.ParamSegs {
		newSeg := FcFnSeg{[]Fc{}}
		for _, param := range seg.Params {
			newParam, err := param.Instantiate(uniParamConParamMap)
			if err != nil {
				return nil, err
			}
			newSeg.Params = append(newSeg.Params, newParam)
		}
		newFc.ParamSegs = append(newFc.ParamSegs, &newSeg)
	}

	return &newFc, nil
}

func (stmt *ConUniFactStmt) InstantiateUniParams(uniParamConParamMap map[string]Fc) (bool, error) {
	// TODO

	return false, nil
}
