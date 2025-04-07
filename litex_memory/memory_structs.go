package litexmemory

import (
	ast "golitex/litex_ast"
	glob "golitex/litex_global"
)

type StoredFactStmt interface {
	String(atom ast.FcAtom) string
}

type StoredSpecFact struct {
	IsTrue bool
	Params []ast.Fc
}

type StoredSpecMemDictNode struct{ Facts []StoredSpecFact }
type SpecFactMemDict struct {
	Dict map[string]map[string]StoredSpecMemDictNode
}

type StoredCondSpecFact struct {
	IsTrue bool
	Params []ast.Fc
	Fact   *ast.CondFactStmt
}

type StoredCondFuncMemDictNode struct {
	Facts []StoredCondSpecFact
}

type CondFactMemDict struct {
	SpecFactsDict map[string]map[string]StoredCondFuncMemDictNode
}

type StoredUniSpecFact struct {
	IsTrue     bool
	FuncParams *[]ast.Fc // 和存在Fact里的FuncFact共享slice，只要是共享，那我就用*[]，虽然确实 Fact里的 FuncFact 日后不会改变，且二者再也不相见了
	Fact       *ast.ConUniFactStmt
}

type StoredUniFuncMemDictNode struct {
	Facts []StoredUniSpecFact
}

type UniFactMemDict struct {
	SpecFactsDict map[string]map[string]StoredUniFuncMemDictNode
}

type EqualFactMemoryTreeNode struct {
	FcAsKey ast.Fc
	// 完全共享的情况，通常是非常本质的情况，比如litex里保存 = 相关的事实的时候，如果 x1, x2, .. xn 都相等，那他们 共享同一片地址，这个地址里存了 [x1, x2 .., xn]。如果我新来一个 y = xm，那x1, x2, … xn, y一起指向 [x1, x2, … xn, y]，即任何 xm 都能 修改 和自己相等的key 所指向的那片地址
	Values *[]ast.Fc // VERY IMPORTANT: THIS IS PTR TO SLICE, NOT SLICE, Because every owner of this piece of memory can modify it, and this modification is shared between owners (every owner can see this modification).
	// 如果一个prop没有同时 有传递性(a = b. b = c => a = c)和交换性(know a = b 和 now b =a 等价)，那就不会共享内存。
}

type EqualFactMem struct {
	Mem glob.RedBlackTree[*EqualFactMemoryTreeNode]
}

type StoredPropMemDictNode struct{ Def *ast.DefConPropStmt }

type PropMem struct {
	// 之所以是 map[string][string] 而不是 map[string]，因为虽然用户在当前的项目里，始终第一个key是""，但如果我读入了来自其他地方的包，那就是另外一个名字了
	Dict map[string]map[string]StoredPropMemDictNode
}

type StoredObjMemDictNode struct{ Def *ast.DefObjStmt }
type ObjMem struct {
	Dict map[string]map[string]StoredObjMemDictNode
}

type FnMem struct {
	Dict map[string]map[string]StoredFnMemDictNode
}

type StoredFnMemDictNode struct{ Def *ast.DefConFnStmt }
