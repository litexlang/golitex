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

func compareFcFnParams(knownPair parser.FcFnSeg, givenPair parser.FcFnSeg) (int, error) {
	if len(knownPair.Params) != len(givenPair.Params) {
		return len(knownPair.Params) - len(givenPair.Params), nil
	}

	for i := 0; i < len(knownPair.Params); i++ {
		if comp, err := CompareFc(knownPair.Params[i], givenPair.Params[i]); comp != 0 || err != nil {
			return comp, err
		}
	}

	return 0, nil
}

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
	const (
		relationSpecFactStmtEnum = 0
		funcSpecFactEnum         = 1
	)
	switch (fact).(type) {
	case *parser.RelationFactStmt:
		return relationSpecFactStmtEnum, nil
	case *parser.FuncFactStmt:
		return funcSpecFactEnum, nil
	}

	return 0, fmt.Errorf("unknown SpecFactStmt type: %T", fact)
}

func (env *Env) NewCondFact(fact *parser.ConditionalFactStmt) error {
	for _, f := range fact.ThenFacts {
		node, err := env.CondFactMemory.Mem.Search(&CondFactMemoryNode{f, []*parser.ConditionalFactStmt{}})
		if err != nil {
			return err
		}
		if node != nil {
			node.Key.CondFacts = append(node.Key.CondFacts, fact)
		} else {
			err := env.CondFactMemory.Mem.Insert(&CondFactMemoryNode{f, []*parser.ConditionalFactStmt{fact}})
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
