package litexmemory

import (
	"fmt"
	parser "golitex/litex_parser"
)

func specFactCompare(knownFact parser.SpecFactStmt, givenFact parser.SpecFactStmt) (int, error) {
	// First, compare the types of the facts
	if specTypeCompareResult, err := specFactTypeCompare(knownFact, givenFact); specTypeCompareResult != 0 || err != nil {
		return specTypeCompareResult, err
	}

	// If the types are the same, compare the values based on the specific type
	switch known := knownFact.(type) {
	case *parser.RelationFactStmt:
		if given, ok := givenFact.(*parser.RelationFactStmt); ok {
			return specRelationFactCompare(known, given)
		}
	case *parser.FuncFactStmt:
		if given, ok := givenFact.(*parser.FuncFactStmt); ok {
			return specFuncFactCompare(known, given)
		}
	default:
		return 0, fmt.Errorf("unknown spec fact type")
	}

	return 0, fmt.Errorf("unknown spec fact")
}

func specRelationFactCompare(knownFact *RelationFactMemoryNode, givenFact *RelationFactMemoryNode) (int, error) {
	panic("TODO not implemented")
}

const (
	isTrueEnum    = 0
	isNotTrueEnum = 1
)

func specFuncIsTrueCompare(knownFact *parser.FuncFactStmt, givenFact *parser.FuncFactStmt) int {
	knownFactIsTrueEnum := isTrueEnum
	if !knownFact.IsTrue {
		knownFactIsTrueEnum = isNotTrueEnum
	}

	givenFactIsTrueEnum := isTrueEnum
	if !givenFact.IsTrue {
		givenFactIsTrueEnum = isNotTrueEnum
	}

	return knownFactIsTrueEnum - givenFactIsTrueEnum
}

func specFuncFactCompare(knownFact *FuncFactMemoryNode, givenFact *FuncFactMemoryNode) (int, error) {
	if isTrueComp := specFuncIsTrueCompare(knownFact, givenFact); isTrueComp != 0 {
		return isTrueComp, nil
	}

	return CompareFc(knownFact.Fc, givenFact.Fc)
}

const (
	fcStrEnum        = 0
	fcFnRetValueEnum = 1
	// FcMemChainEnum   = 2
)

func getFcEnum(fc parser.Fc) (int, error) {
	_, ok := fc.(parser.FcStr)
	if ok {
		return fcStrEnum, nil
	}

	_, ok = fc.(*parser.FcFnRetValue)
	if ok {
		return fcFnRetValueEnum, nil
	}

	// _, ok = fc.(*parser.FcChain)
	// if ok {
	// 	return FcMemChainEnum, nil
	// }

	return 0, fmt.Errorf("unknown Fc type: %T", fc)
}

func CompareFc(knownFc parser.Fc, givenFc parser.Fc) (int, error) {
	if typeComp, err := compareFcType(knownFc, givenFc); typeComp != 0 || err != nil {
		return typeComp, err
	}

	return compareFcOfTheSameType(knownFc, givenFc)
}

func compareFcOfTheSameType(knownFc parser.Fc, givenFc parser.Fc) (int, error) {
	knownFcStr, ok := knownFc.(parser.FcStr)
	givenFcStr, ok2 := givenFc.(parser.FcStr)
	if ok && ok2 {
		return compareFcStr(knownFcStr, givenFcStr)
	}

	knownFcFnRetValue, ok := knownFc.(*parser.FcFnRetValue)
	givenFcFnRetValue, ok2 := givenFc.(*parser.FcFnRetValue)
	if ok && ok2 {
		return compareFcFnRetValue(knownFcFnRetValue, givenFcFnRetValue)
	}

	// knownFcMemChain, ok := knownFc.(*parser.FcChain)
	// givenFcMemChain, ok2 := givenFc.(*parser.FcChain)
	// if ok && ok2 {
	// 	return compareFcMemChain(knownFcMemChain, givenFcMemChain)
	// }

	return 0, fmt.Errorf("unknown fc type")
}

func compareFcStr(knownFc parser.FcStr, givenFc parser.FcStr) (int, error) {
	if len(knownFc.Value) != len(givenFc.Value) {
		return len(knownFc.Value) - len(givenFc.Value), nil
	}

	for i := 0; i < len(knownFc.Value); i++ {
		if knownFc.Value[i] != givenFc.Value[i] {
			return int(knownFc.Value[i]) - int(givenFc.Value[i]), nil
		}
	}

	return 0, nil
}

// func compareTypeObjStr(knownFc parser.TypeObjStr, givenFc parser.TypeObjStr) (int, error) {
// 	if len(knownFc) != len(givenFc) {
// 		return len(knownFc) - len(givenFc), nil
// 	}

// 	for i := 0; i < len(knownFc); i++ {
// 		if knownFc[i] != givenFc[i] {
// 			return int(knownFc[i]) - int(givenFc[i]), nil
// 		}
// 	}

// 	return 0, nil
// }

func compareTypeParamsAndParamsPair(knownPair parser.ObjParams, givenPair parser.ObjParams) (int, error) {
	// if len(knownPair.TypeParams) != len(givenPair.TypeParams) {
	// 	return len(knownPair.TypeParams) - len(givenPair.TypeParams), nil
	// }

	// for i := 0; i < len(knownPair.TypeParams); i++ {
	// 	if comp, err := compareTypeObjStr(knownPair.TypeParams[i], givenPair.TypeParams[i]); comp != 0 || err != nil {
	// 		return comp, err
	// 	}
	// }

	if len(knownPair.ObjParams) != len(givenPair.ObjParams) {
		return len(knownPair.ObjParams) - len(givenPair.ObjParams), nil
	}

	for i := 0; i < len(knownPair.ObjParams); i++ {
		if comp, err := CompareFc(knownPair.ObjParams[i], givenPair.ObjParams[i]); comp != 0 || err != nil {
			return comp, err
		}
	}

	return 0, nil
}

func compareFcFnRetValue(knownFc *parser.FcFnRetValue, givenFc *parser.FcFnRetValue) (int, error) {
	if comp, err := compareFcStr(knownFc.FnName, givenFc.FnName); comp != 0 || err != nil {
		return comp, err
	}

	if len(knownFc.TypeParamsObjParamsPairs) != len(givenFc.TypeParamsObjParamsPairs) {
		return len(knownFc.TypeParamsObjParamsPairs) - len(givenFc.TypeParamsObjParamsPairs), nil
	}

	for i := 0; i < len(knownFc.TypeParamsObjParamsPairs); i++ {
		if comp, err := compareTypeParamsAndParamsPair(knownFc.TypeParamsObjParamsPairs[i], givenFc.TypeParamsObjParamsPairs[i]); comp != 0 || err != nil {
			return comp, err
		}
	}

	return 0, nil
}

// func compareFcMemChain(knownFc *parser.FcChain, givenFc *parser.FcChain) (int, error) {
// 	if len(knownFc.ChainOfMembers) != len(givenFc.ChainOfMembers) {
// 		return len(knownFc.ChainOfMembers) - len(givenFc.ChainOfMembers), nil
// 	}

// 	for i := 0; i < len(knownFc.ChainOfMembers); i++ {
// 		if comp, err := CompareFc((knownFc.ChainOfMembers)[i], (givenFc.ChainOfMembers)[i]); comp != 0 || err != nil {
// 			return comp, err
// 		}
// 	}

// 	return 0, nil
// }

func compareFcType(knownFc parser.Fc, givenFc parser.Fc) (int, error) {
	knownFcEnum, err := getFcEnum(knownFc)
	if err != nil {
		return 0, err
	}

	givenFcEnum, err := getFcEnum(givenFc)
	if err != nil {
		return 0, err
	}

	return knownFcEnum - givenFcEnum, nil
}

const (
	relationSpecFactStmtEnum = 0
	funcSpecFactEnum         = 1
)

func specFactTypeCompare(knownFact parser.SpecFactStmt, givenFact parser.SpecFactStmt) (int, error) {
	knownFactType, err := getSpecFactEnum(knownFact)
	if err != nil {
		return 0, err
	}

	givenFactType, err := getSpecFactEnum(givenFact)
	if err != nil {
		return 0, err
	}

	return knownFactType - givenFactType, nil
}

func getSpecFactEnum(fact parser.SpecFactStmt) (int, error) {

	switch (fact).(type) {
	case *parser.RelationFactStmt:
		return relationSpecFactStmtEnum, nil
	case *parser.FuncFactStmt:
		return funcSpecFactEnum, nil
	}

	return 0, fmt.Errorf("unknown SpecFactStmt type: %T", fact)
}

func (env *Env) NewCondFact(fact *parser.WhenCondFactStmt) error {
	for _, f := range fact.ThenFacts {
		node, err := env.CondFactMemory.Mem.Search(&CondFactMemoryNode{f, []*parser.WhenCondFactStmt{}})
		if err != nil {
			return err
		}
		if node != nil {
			node.Key.CondFacts = append(node.Key.CondFacts, fact)
		} else {
			err := env.CondFactMemory.Mem.Insert(&CondFactMemoryNode{f, []*parser.WhenCondFactStmt{fact}})
			if err != nil {
				return err
			}
		}
	}
	return nil
}

func CondFactMemoryTreeNodeCompare(knownFact *CondFactMemoryNode, givenFact *CondFactMemoryNode) (int, error) {
	return specFactCompare(knownFact.ThenFactAsKey, givenFact.ThenFactAsKey)
}

func EqualFactMemoryTreeNodeCompare(knownFact *EqualFactMemoryTreeNode, givenFact *EqualFactMemoryTreeNode) (int, error) {
	return CompareFc(knownFact.FcAsKey, givenFact.FcAsKey)
}

func UniFactMemoryTreeNodeCompare(knownFact *UniFactMemoryTreeNode, givenFact *UniFactMemoryTreeNode) (int, error) {
	panic("")
}
