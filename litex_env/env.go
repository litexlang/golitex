package litexmemory

import (
	cmp "golitex/litex_comparator"
	ds "golitex/litex_data_structure"
	mem "golitex/litex_memory"
)

type Env struct {
	Parent *Env

	ObjMem  mem.ObjMem
	PropMem mem.PropMem
	FnMem   mem.FnMem

	// 这里必须区分Concrete和Generic. 默认不加前缀的是普通的事实；有Generic前缀的是Generic
	FuncFactMem mem.FuncFactMemDict
	CondFactMem mem.CondFactMemDict
	// RelaFactMem  mem.RelaFactMemDict
	UniFactMem   mem.UniFactMemDict
	EqualFactMem mem.EqualFactMem
}

func NewEnv(parent *Env) *Env {
	env := &Env{
		Parent: parent,

		ObjMem:  *mem.NewObjMemory(),
		PropMem: *mem.NewPropMemory(),
		FnMem:   *mem.NewFnMemory(),

		FuncFactMem: *mem.NewFuncFactMemDict(),
		CondFactMem: *mem.NewCondFactMemDict(),
		// RelaFactMem: mem.RelaFactMemDict{},

		// ConcreteFuncFactMemory:     mem.ConcreteFuncFactMemory{Mem: *ds.NewRedBlackTree(cmp.CmpSpecFuncFact)}, // 需要把env包和memory包分离的一个原因就是，这里会引入cmp，而cmp包要用mem的节点，会cyclic
		// ConcreteRelationFactMemory: mem.ConcreteRelationFactMemory{Mem: *ds.NewRedBlackTree(cmp.SpecRelationFactCompare)},
		// ConcreteCondFactMemory:     mem.ConcreteCondFactMemory{Mem: *ds.NewRedBlackTree(cmp.CondFactMemoryTreeNodeCompare)},
		// UniFactMemory:      *NewUniFactMemory(),
		UniFactMem:   mem.UniFactMemDict{},
		EqualFactMem: mem.EqualFactMem{Mem: *ds.NewRedBlackTree(cmp.EqualFactMemoryTreeNodeCompare)},
	}

	return env
}
