package litexcomparator

import (
	mem "golitex/litex_memory"
)

func SpecRelationFactCompare(left, right *mem.RelationFactMemoryNode) (int, error) {
	panic("TODO not implemented")
}

func CondFactMemoryTreeNodeCompare(left, right *mem.CondFactMemoryNode) (int, error) {
	return CmpSpecFact(left.ThenFactAsKey, right.ThenFactAsKey)
}

func EqualFactMemoryTreeNodeCompare(knownFact, givenFact *mem.EqualFactMemoryTreeNode) (int, error) {
	return CmpFc(knownFact.FcAsKey, givenFact.FcAsKey)
}

func UniFactMemoryTreeNodeCompare(knownFact, givenFact *mem.UniFactMemoryTreeNode) (int, error) {
	panic("")
}
