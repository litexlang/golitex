package litexmemory

import (
	cmp "golitex/litex_comparator"
	glob "golitex/litex_global"
	mem "golitex/litex_memory"
	parser "golitex/litex_parser"
)

type Env struct {
	Parent *Env

	ObjMem  mem.ObjMem
	PropMem mem.PropMem
	FnMem   mem.FnMem

	// 这里必须区分Concrete和Generic. 默认不加前缀的是普通的事实；有Generic前缀的是Generic
	SpecFactMem mem.SpecFactMemDict
	CondFactMem mem.CondFactMemDict
	// RelaFactMem  mem.RelaFactMemDict
	UniFactMem   mem.UniFactMemDict
	EqualFactMem mem.EqualFactMem

	UniParamMap map[string]parser.Fc
}

func NewEnv(parent *Env, uniParamMapPtr *map[string]parser.Fc) *Env {
	if uniParamMapPtr == nil {
		uniParamMap := make(map[string]parser.Fc)
		uniParamMapPtr = &uniParamMap
	}

	env := &Env{
		Parent: parent,

		ObjMem:  *mem.NewObjMemory(),
		PropMem: *mem.NewPropMemory(),
		FnMem:   *mem.NewFnMemory(),

		SpecFactMem:  *mem.NewSpecFactMemDict(),
		CondFactMem:  *mem.NewCondFactMemDict(),
		UniFactMem:   *mem.NewUniFactMemDict(),
		EqualFactMem: *newEqualFactMem(),
		UniParamMap:  *uniParamMapPtr,
	}

	return env
}

func newEqualFactMem() *mem.EqualFactMem {
	return &mem.EqualFactMem{Mem: *glob.NewRedBlackTree(cmp.EqualFactMemoryTreeNodeCompare)}
}
