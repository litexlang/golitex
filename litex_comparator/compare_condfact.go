package litexcomparator

import (
	mem "golitex/litex_memory"
)

func CondFactMemoryTreeNodeCompare(left, right *mem.CondFactMemoryNode) (int, error) {
	return CmpSpecFact(left.ThenFactAsKey, right.ThenFactAsKey)
}
