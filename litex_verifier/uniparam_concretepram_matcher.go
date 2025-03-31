package litexverifier

import (
	mem "golitex/litex_memory"
	parser "golitex/litex_parser"
)

func MatchStoredUniSpaceFactAndSpecFact(knownFact mem.StoredUniSpecFact, stmt *parser.SpecFactStmt) (*map[string][]parser.Fc, bool, error) { // 之所以是*map[string][]parser.Fc而不是 *map[string]parser.Fc, 因为可能用户输入的是字面量相同，实际意义一样的obj
	if len(stmt.Params) != len(*knownFact.FuncParams) {
		// TODO 之后要根除不匹配的情况
		return nil, false, nil
	}

	for i, uniParam := range *knownFact.FuncParams {
		if matchMap, matched, err := MatchUniConcreteParams(uniParam, stmt.Params[i], knownFact.UniParams); err != nil {
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

func MatchUniConcreteParams(uniFuncParam parser.Fc, concreteFuncParam parser.Fc, possibleUniParams *[]string) (*map[string][]parser.Fc, bool, error) {
	retMap := make(map[string][]parser.Fc)

	if asAtom := uniFuncParam.(*parser.FcAtom); asAtom != nil {
		return matchAtomUniConcreteParams(asAtom, concreteFuncParam, possibleUniParams)
	}

	return &retMap, true, nil
}

func matchAtomUniConcreteParams(uniFuncAtom *parser.FcAtom, concreteFuncParam parser.Fc, possibleUniParams *[]string) (*map[string][]parser.Fc, bool, error) {
	retMap := make(map[string][]parser.Fc)

	if matchStr, ok := isUniParam(uniFuncAtom, possibleUniParams); ok {
		retMap[matchStr] = []parser.Fc{concreteFuncParam}
		return &retMap, true, nil
	}

	// TODO: Verify uniFuncAtom 是否和 concreteFuncParam 是一样的

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
