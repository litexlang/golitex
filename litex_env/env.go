package litexmemory

import (
	cmp "golitex/litex_comparator"
	glob "golitex/litex_global"
	mem "golitex/litex_memory"
	st "golitex/litex_statements"
)

type Env struct {
	Parent *Env
	Msgs   []string

	ObjMem  mem.ObjMem
	PropMem mem.PropMem
	FnMem   mem.FnMem

	SpecFactMem  mem.SpecFactMemDict
	CondFactMem  mem.CondFactMemDict
	UniFactMem   mem.UniFactMemDict
	EqualFactMem mem.EqualFactMem

	//TODO 这里必须区分Concrete和Generic. 默认不加前缀的是普通的事实；有Generic前缀的是Generic

	UniParamMap map[string]st.Fc

	CurPkg string
}

func NewEnv(parent *Env, uniParamMap map[string]st.Fc, curPkg string) *Env {
	if uniParamMap == nil {
		uniParamMap = make(map[string]st.Fc)
	}

	env := &Env{
		Parent: parent,
		Msgs:   []string{},

		ObjMem:  *mem.NewObjMemory(),
		PropMem: *mem.NewPropMemory(),
		FnMem:   *mem.NewFnMemory(),

		SpecFactMem:  *mem.NewSpecFactMemDict(),
		CondFactMem:  *mem.NewCondFactMemDict(),
		UniFactMem:   *mem.NewUniFactMemDict(),
		EqualFactMem: *newEqualFactMem(),

		UniParamMap: uniParamMap,

		CurPkg: curPkg,
	}

	return env
}

func newEqualFactMem() *mem.EqualFactMem {
	return &mem.EqualFactMem{Mem: *glob.NewRedBlackTree(cmp.EqualFactMemoryTreeNodeCompare)}
}

func (e *Env) NewMsg(s string) {
	e.Msgs = append(e.Msgs, s)
}
