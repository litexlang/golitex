package litexmemory

import (
	glob "golitex/litex_global"
	parser "golitex/litex_parser"
)

type StoredFactStmt interface {
	String(atom parser.FcAtom) string
}

type StoredSpecFact struct {
	IsTrue bool
	Params []parser.Fc
}

type StoredSpecMemDictNode struct{ Facts []StoredSpecFact }
type SpecFactMemDict struct {
	Dict map[string]map[string]StoredSpecMemDictNode
}

type StoredCondSpecFact struct {
	IsTrue bool
	Params []parser.Fc
	Fact   *parser.CondFactStmt
}

type StoredCondFuncMemDictNode struct {
	Facts []StoredCondSpecFact
}

type CondFactMemDict struct {
	SpecFactsDict map[string]map[string]StoredCondFuncMemDictNode
}

type StoredUniSpecFact struct {
	IsTrue     bool
	FuncParams []parser.Fc // 和存在Fact里的FuncFact共享slice，但因为后续不再修改了，所以这里不用取 *[]parser.Fc
	// UniParams  *[]string
	Fact *parser.UniFactStmt
}

type StoredUniFuncMemDictNode struct {
	Facts []StoredUniSpecFact
}

type UniFactMemDict struct {
	SpecFactsDict map[string]map[string]StoredUniFuncMemDictNode
}

type EqualFactMemoryTreeNode struct {
	FcAsKey parser.Fc
	// 完全共享的情况，通常是非常本质的情况，比如litex里保存 = 相关的事实的时候，如果 x1, x2, .. xn 都相等，那他们 共享同一片地址，这个地址里存了 [x1, x2 .., xn]。如果我新来一个 y = xm，那x1, x2, … xn, y一起指向 [x1, x2, … xn, y]，即任何 xm 都能 修改 和自己相等的key 所指向的那片地址
	Values *[]parser.Fc // VERY IMPORTANT: THIS IS PTR TO SLICE, NOT SLICE, Because every owner of this piece of memory can modify it, and this modification is shared between owners (every owner can see this modification).
	// 如果一个prop没有同时 有传递性(a = b. b = c => a = c)和交换性(know a = b 和 now b =a 等价)，那就不会共享内存。
}

type EqualFactMem struct {
	Mem glob.RedBlackTree[*EqualFactMemoryTreeNode]
}

type ObjMemoryEntry struct {
}

type StoredPropMemDictNode struct{ Def *parser.DefConPropStmt }

type PropMem struct {
	Dict map[string]map[string]StoredPropMemDictNode
}

type PropMemoryEntry struct {
}

type FnMem struct {
}

type FnMemEntry struct {
}

type ObjMem struct {
}
