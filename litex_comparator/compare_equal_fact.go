package litexcomparator

import (
	mem "golitex/litex_memory"
)

func EqualFactMemoryTreeNodeCompare(left, right *mem.EqualFactMemoryTreeNode) (int, error) {
	return CmpFcLiterally(left.FcAsKey, right.FcAsKey)
}
