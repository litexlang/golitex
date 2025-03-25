package litexcomparator

import (
	mem "golitex/litex_memory"
)

func EqualFactMemoryTreeNodeCompare(left, right *mem.EqualFactMemoryTreeNode) (int, error) {
	return CmpFc(left.FcAsKey, right.FcAsKey)
}
