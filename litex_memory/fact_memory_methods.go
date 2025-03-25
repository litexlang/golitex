package litexmemory

func specRelationFactCompare(left, right *RelationFactMemoryNode) (int, error) {
	panic("TODO not implemented")
}

func CondFactMemoryTreeNodeCompare(left, right *CondFactMemoryNode) (int, error) {
	return specFactCompare(left.ThenFactAsKey, right.ThenFactAsKey)
}

func EqualFactMemoryTreeNodeCompare(knownFact *EqualFactMemoryTreeNode, givenFact *EqualFactMemoryTreeNode) (int, error) {
	return CompareFc(knownFact.FcAsKey, givenFact.FcAsKey)
}

func UniFactMemoryTreeNodeCompare(knownFact *UniFactMemoryTreeNode, givenFact *UniFactMemoryTreeNode) (int, error) {
	panic("")
}
