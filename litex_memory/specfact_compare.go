// REMARK：Compare和Search是分离的。Compare函数不能引入env信息。只是纯的Fc比较，和env无关。
package litexmemory

import (
	"fmt"
	parser "golitex/litex_parser"
)

func specFactCompare(left, right parser.SpecFactStmt) (int, error) {
	// First, compare the types of the facts
	if specTypeCompareResult, err := specFactTypeCompare(left, right); specTypeCompareResult != 0 || err != nil {
		return specTypeCompareResult, err
	}

	// If the types are the same, compare the values based on the specific type
	switch known := left.(type) {
	case *parser.FuncFactStmt:
		if given, ok := right.(*parser.FuncFactStmt); ok {
			return specFuncFactCompare(known, given)
		}
	case *parser.RelationFactStmt:
		if given, ok := right.(*parser.RelationFactStmt); ok {
			return specRelationFactCompare(known, given)
		}
	default:
		return 0, fmt.Errorf("unknown spec fact type")
	}

	return 0, fmt.Errorf("unknown spec fact")
}

func specFactTypeCompare(left, right parser.SpecFactStmt) (int, error) {
	const (
		funcSpecFactEnum         = 0
		relationSpecFactStmtEnum = 1
	)

	// Process knownFact
	var knownFactType int
	switch left.(type) {
	case *parser.RelationFactStmt:
		knownFactType = relationSpecFactStmtEnum
	case *parser.FuncFactStmt:
		knownFactType = funcSpecFactEnum
	default:
		return 0, fmt.Errorf("unknown SpecFactStmt type: %T", left)
	}

	// Process givenFact
	var givenFactType int
	switch right.(type) {
	case *parser.RelationFactStmt:
		givenFactType = relationSpecFactStmtEnum
	case *parser.FuncFactStmt:
		givenFactType = funcSpecFactEnum
	default:
		return 0, fmt.Errorf("unknown SpecFactStmt type: %T", right)
	}

	return knownFactType - givenFactType, nil
}

func specFuncFactCompare(left, right *FuncFactMemoryNode) (int, error) {
	if isTrueComp := specFuncIsTrueCompare(left, right); isTrueComp != 0 {
		return isTrueComp, nil
	}

	return CompareFc(&left.Opt, &right.Opt)
}

func specFuncIsTrueCompare(left, right *parser.FuncFactStmt) int {
	const (
		isTrueEnum    = 0
		isNotTrueEnum = 1
	)

	knownFactIsTrueEnum := isTrueEnum
	if !left.IsTrue {
		knownFactIsTrueEnum = isNotTrueEnum
	}

	givenFactIsTrueEnum := isTrueEnum
	if !right.IsTrue {
		givenFactIsTrueEnum = isNotTrueEnum
	}

	return knownFactIsTrueEnum - givenFactIsTrueEnum
}
