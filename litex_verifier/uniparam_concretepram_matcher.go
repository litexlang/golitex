package litexverifier

import (
	"fmt"
	mem "golitex/litex_memory"
	parser "golitex/litex_parser"
)

// Con means Concrete
func (ver *Verifier) matchStoredUniConSpecFacts(knownFact mem.StoredUniSpecFact, stmt *parser.SpecFactStmt) (*map[string][]parser.Fc, bool, error) { // 之所以是*map[string][]parser.Fc而不是 *map[string]parser.Fc, 因为可能用户输入的是字面量相同，实际意义一样的obj
	if len(stmt.Params) != len(*knownFact.FuncParams) {
		return nil, false, nil
	}

	for i, uniParam := range *knownFact.FuncParams {
		if matchMap, matched, err := ver.matchUniConParams(uniParam, stmt.Params[i], knownFact.UniParams); err != nil {
			return nil, false, nil
		} else if !matched {
			return nil, false, nil
		} else {
			// TODO
			_ = matchMap
		}
	}

	return nil, false, nil
}

func (ver *Verifier) matchUniConParams(uniFuncParam parser.Fc, concreteFuncParam parser.Fc, possibleUniParams *[]string) (*map[string][]parser.Fc, bool, error) {
	if asAtom := uniFuncParam.(*parser.FcAtom); asAtom != nil {
		return ver.matchAtomUniConParams(asAtom, concreteFuncParam, possibleUniParams)
	}

	if asFn := uniFuncParam.(*parser.FcFnCallPipe); asFn != nil {
		return ver.matchFnUniConParams(asFn, concreteFuncParam, possibleUniParams)
	}

	return nil, false, fmt.Errorf("unexpected type of %v", uniFuncParam.String())
}

func (ver *Verifier) matchAtomUniConParams(uniFuncFcAtom *parser.FcAtom, conFuncParam parser.Fc, possibleUniParams *[]string) (*map[string][]parser.Fc, bool, error) {
	retMap := make(map[string][]parser.Fc)

	if matchStr, ok := isUniParam(uniFuncFcAtom, possibleUniParams); ok {
		retMap[matchStr] = []parser.Fc{conFuncParam}
		return &retMap, true, nil
	}

	if ok, err := ver.fcEqualSpec(uniFuncFcAtom, conFuncParam); err != nil {
		return nil, false, err
	} else if ok {
		return &retMap, true, nil
	}

	return nil, false, nil
}

func (ver *Verifier) matchFnUniConParams(uniFuncFcFn *parser.FcFnCallPipe, conFuncParam parser.Fc, possibleUniParams *[]string) (*map[string][]parser.Fc, bool, error) {
	// TODO
	return nil, false, nil
}

func isUniParam(uniFuncAtom *parser.FcAtom, possibleUniParams *[]string) (string, bool) { // ret: matched possible uniParam string; isMatched?
	for _, possible := range *possibleUniParams {
		if possible == uniFuncAtom.OptName && uniFuncAtom.PkgName == "" {
			return possible, true
		}
	}
	return "", false
}
