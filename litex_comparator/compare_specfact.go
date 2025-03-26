package litexcomparator

// import (
// 	"fmt"
// 	mem "golitex/litex_memory"
// 	parser "golitex/litex_parser"
// )

// func CmpSpecFact(left, right parser.SpecFactStmt) (int, error) {
// 	if specTypeCompareResult, err := cmpSpecFactType(left, right); specTypeCompareResult != 0 || err != nil {
// 		return specTypeCompareResult, err
// 	}

// 	switch known := left.(type) {
// 	case *parser.FuncFactStmt:
// 		if given, ok := right.(*parser.FuncFactStmt); ok {
// 			return CmpSpecFuncFact(known, given)
// 		}
// 	case *parser.RelationFactStmt:
// 		if given, ok := right.(*parser.RelationFactStmt); ok {
// 			return SpecRelationFactCompare(known, given)
// 		}
// 	default:
// 		return 0, fmt.Errorf("unknown spec fact type")
// 	}

// 	return 0, fmt.Errorf("unknown spec fact")
// }

// func SpecRelationFactCompare(left, right *mem.RelationFactMemoryNode) (int, error) {
// 	panic("TODO not implemented")
// }

// func cmpSpecFactType(left, right parser.SpecFactStmt) (int, error) {
// 	const (
// 		funcSpecFactEnum         = 0
// 		relationSpecFactStmtEnum = 1
// 	)

// 	knownFactType := 0
// 	switch left.(type) {
// 	case *parser.RelationFactStmt:
// 		knownFactType = relationSpecFactStmtEnum
// 	case *parser.FuncFactStmt:
// 		knownFactType = funcSpecFactEnum
// 	default:
// 		return 0, fmt.Errorf("unknown SpecFactStmt type: %T", left)
// 	}

// 	givenFactType := 0
// 	switch right.(type) {
// 	case *parser.RelationFactStmt:
// 		givenFactType = relationSpecFactStmtEnum
// 	case *parser.FuncFactStmt:
// 		givenFactType = funcSpecFactEnum
// 	default:
// 		return 0, fmt.Errorf("unknown SpecFactStmt type: %T", right)
// 	}

// 	return knownFactType - givenFactType, nil
// }

// func CmpSpecFuncFact(left, right *mem.FuncFactMemoryNode) (int, error) {
// 	if isTrueComp := cmpSpecFuncIsTrue(left, right); isTrueComp != 0 {
// 		return isTrueComp, nil
// 	}

// 	optCmpOut, err := CmpFc(&left.Opt, &right.Opt)
// 	if err != nil {
// 		return 0, err
// 	}
// 	if optCmpOut != 0 {
// 		return optCmpOut, nil
// 	}

// 	leftParamLen := len(left.Params)
// 	rightParamLen := len(right.Params)

// 	if leftParamLen != rightParamLen {
// 		return leftParamLen - rightParamLen, nil
// 	}

// 	for i := 0; i < leftParamLen; i++ {
// 		out, err := CmpFc(left.Params[i], right.Params[i])
// 		if err != nil {
// 			return 0, err
// 		}
// 		if out != 0 {
// 			return out, nil
// 		}
// 	}

// 	return 0, nil
// }

// func cmpSpecFuncIsTrue(left, right *parser.FuncFactStmt) int {
// 	const (
// 		isTrueEnum    = 0
// 		isNotTrueEnum = 1
// 	)

// 	knownFactIsTrueEnum := isTrueEnum
// 	if !left.IsTrue {
// 		knownFactIsTrueEnum = isNotTrueEnum
// 	}

// 	givenFactIsTrueEnum := isTrueEnum
// 	if !right.IsTrue {
// 		givenFactIsTrueEnum = isNotTrueEnum
// 	}

// 	return knownFactIsTrueEnum - givenFactIsTrueEnum
// }
