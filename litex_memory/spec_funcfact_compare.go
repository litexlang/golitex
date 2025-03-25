// REMARK：Compare和Search是分离的。Compare函数不能引入env信息。只是纯的Fc比较，和env无关。
package litexmemory

import (
	parser "golitex/litex_parser"
)

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
