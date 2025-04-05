package litexverifier

import (
	"fmt"
	mem "golitex/litex_memory"
	parser "golitex/litex_parser"
)

// match 函数不需要传入state: 没有any, spec 之分，也不需要打印
func (ver *Verifier) matchStoredUniConSpecFacts(knownFact mem.StoredUniSpecFact, stmt *parser.SpecFactStmt) (map[string][]parser.Fc, bool, error) { // 之所以是map[string][]parser.Fc而不是 map[string]parser.Fc, 因为可能用户输入的是字面量相同，实际意义一样的obj
	if len(stmt.Params) != len(*knownFact.FuncParams) {
		return nil, false, nil
	}

	retMap := map[string][]parser.Fc{}

	for i, uniParam := range *knownFact.FuncParams {
		matchMap, matched, err := ver.matchUniConFc(uniParam, stmt.Params[i], knownFact.Fact.Params)
		if err != nil {
			return nil, false, err
		}
		if !matched {
			return nil, false, nil
		}
		mergeMatchMaps(matchMap, retMap)
	}

	return retMap, true, nil
}

func (ver *Verifier) matchUniConFc(uniFuncParam parser.Fc, concreteFuncParam parser.Fc, possibleUniParams []string) (map[string][]parser.Fc, bool, error) {
	// Safe type switching
	switch param := uniFuncParam.(type) {
	case *parser.FcAtom:
		return ver.matchAtomUniConFc(param, concreteFuncParam, possibleUniParams)
	case *parser.FcFnPipe:
		return ver.matchFnUniConFc(param, concreteFuncParam, possibleUniParams)
	default:
		return nil, false, fmt.Errorf("unexpected type %T for parameter %v", param, uniFuncParam.String())
	}
}

func (ver *Verifier) matchAtomUniConFc(uniFuncFcAtom *parser.FcAtom, conFuncParam parser.Fc, possibleUniParams []string) (map[string][]parser.Fc, bool, error) {
	retMap := make(map[string][]parser.Fc)

	if matchStr, ok := isUniParam(uniFuncFcAtom, possibleUniParams); ok {
		retMap[matchStr] = []parser.Fc{conFuncParam}
		return retMap, true, nil
	}

	ok, err := ver.fcEqualSpec(uniFuncFcAtom, conFuncParam, SpecNoMsg)
	if err != nil {
		return nil, false, err
	}
	if ok {
		return retMap, true, nil
	}

	return nil, false, nil
}

func (ver *Verifier) matchFnUniConFc(uniFuncFcFn *parser.FcFnPipe, conFuncParam parser.Fc, possibleUniParams []string) (map[string][]parser.Fc, bool, error) {
	retMap := map[string][]parser.Fc{}

	conParamAsFcFn, ok := conFuncParam.(*parser.FcFnPipe)
	if !ok {
		return nil, false, nil
	}

	if matchedStr, ok := isUniParam(&uniFuncFcFn.FnHead, possibleUniParams); ok {
		retMap[matchedStr] = []parser.Fc{&conParamAsFcFn.FnHead}
	} else {
		ok, err := ver.fcEqualSpec(&uniFuncFcFn.FnHead, &conParamAsFcFn.FnHead, SpecNoMsg)
		if err != nil {
			return nil, false, err
		}
		if !ok {
			return nil, false, nil
		}
	}

	if len(conParamAsFcFn.CallPipe) != len(uniFuncFcFn.CallPipe) {
		return nil, false, fmt.Errorf("expect length of %v equal to length of %v", conParamAsFcFn.CallPipe, uniFuncFcFn.CallPipe)
	}

	for i, uniPipe := range uniFuncFcFn.CallPipe {
		if len(uniPipe.Params) != len(conParamAsFcFn.CallPipe[i].Params) {
			return nil, false, fmt.Errorf("expect length of %v equal to length of %v", uniPipe.Params, conParamAsFcFn.CallPipe[i].Params)
		}

		for j, param := range uniPipe.Params {
			matchMap, ok, err := ver.matchUniConFc(param, conParamAsFcFn.CallPipe[i].Params[j], possibleUniParams)
			if err != nil {
				return nil, false, err
			}
			if !ok {
				return nil, false, nil
			}
			mergeMatchMaps(matchMap, retMap)
		}
	}

	return retMap, true, nil
}

func isUniParam(uniFuncAtom *parser.FcAtom, possibleUniParams []string) (string, bool) { // ret: matched possible uniParam string; isMatched?
	for _, possible := range possibleUniParams {
		if possible == uniFuncAtom.Value && uniFuncAtom.PkgName == "" {
			return possible, true
		}
	}
	return "", false
}

func mergeMatchMaps(from map[string][]parser.Fc, to map[string][]parser.Fc) {
	for key, value := range from {
		if _, ok := (to)[key]; ok {
			(to)[key] = append((to)[key], value...)
		} else {
			(to)[key] = value
		}
	}
}
