package litexverifier

import (
	"fmt"
	ast "golitex/litex_ast"
	mem "golitex/litex_memory"
)

// match 函数不需要传入state: 没有any, spec 之分，也不需要打印
func (ver *Verifier) matchStoredUniConSpecFacts(knownFact mem.StoredUniSpecFact, stmt *ast.SpecFactStmt) (map[string][]ast.Fc, bool, error) { // 之所以是map[string][]ast.Fc而不是 map[string]ast.Fc, 因为可能用户输入的是字面量相同，实际意义一样的obj
	if len(stmt.Params) != len(*knownFact.FuncParams) {
		return nil, false, nil
	}

	retMap := map[string][]ast.Fc{}

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

func (ver *Verifier) matchUniConFc(uniFuncParam ast.Fc, concreteFuncParam ast.Fc, possibleUniParams []string) (map[string][]ast.Fc, bool, error) {
	// Safe type switching
	switch param := uniFuncParam.(type) {
	case *ast.FcAtom:
		return ver.matchAtomUniConFc(param, concreteFuncParam, possibleUniParams)
	case *ast.FcFnPipe:
		return ver.matchFnUniConFc(param, concreteFuncParam, possibleUniParams)
	default:
		return nil, false, fmt.Errorf("unexpected type %T for parameter %v", param, uniFuncParam.String())
	}
}

func (ver *Verifier) matchAtomUniConFc(uniFuncFcAtom *ast.FcAtom, conFuncParam ast.Fc, possibleUniParams []string) (map[string][]ast.Fc, bool, error) {
	retMap := make(map[string][]ast.Fc)

	if matchStr, ok := isUniParam(uniFuncFcAtom, possibleUniParams); ok {
		retMap[matchStr] = []ast.Fc{conFuncParam}
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

func (ver *Verifier) matchFnUniConFc(uniFuncFcFn *ast.FcFnPipe, conFuncParam ast.Fc, possibleUniParams []string) (map[string][]ast.Fc, bool, error) {
	retMap := map[string][]ast.Fc{}

	conParamAsFcFn, ok := conFuncParam.(*ast.FcFnPipe)
	if !ok {
		return nil, false, nil
	}

	if matchedStr, ok := isUniParam(&uniFuncFcFn.FnHead, possibleUniParams); ok {
		retMap[matchedStr] = []ast.Fc{&conParamAsFcFn.FnHead}
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
		return nil, false, nil //? 不清楚应该报错还是说直接返回不对，应该是返回不对
	}

	for i, uniPipe := range uniFuncFcFn.CallPipe {
		if len(uniPipe.Params) != len(conParamAsFcFn.CallPipe[i].Params) {
			return nil, false, nil
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

func isUniParam(uniFuncAtom *ast.FcAtom, possibleUniParams []string) (string, bool) { // ret: matched possible uniParam string; isMatched?
	for _, possible := range possibleUniParams {
		if possible == uniFuncAtom.Value && uniFuncAtom.PkgName == "" {
			return possible, true
		}
	}
	return "", false
}

func mergeMatchMaps(from map[string][]ast.Fc, to map[string][]ast.Fc) {
	for key, value := range from {
		if _, ok := (to)[key]; ok {
			(to)[key] = append((to)[key], value...)
		} else {
			(to)[key] = value
		}
	}
}
