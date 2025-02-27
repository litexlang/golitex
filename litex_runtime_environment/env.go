// 约定：var, fn, prop 名不能冲突，即不能有一个变量是var，同时也是Prop
package litexenv

import (
	"fmt"
	memory "golitex/litex_memory"
	pack "golitex/litex_package_management"
	parser "golitex/litex_parser"
)

type Env struct {
	Parent                 *Env
	VarMemory              memory.VarMemory
	PropMemory             memory.PropMemory
	FnMemory               memory.FnMemory
	AliasMemory            memory.AliasMemory
	InstantiatedFactMemory memory.SpecFactMemory
	ConditionalFactMemory  memory.CondFactMemory
	UniversalFactMemory    memory.UniFactMemory
	VarTypeMemory          memory.FcVarTypeMemory
}

func NewEnv() *Env {
	return &Env{
		Parent:                 nil,
		VarMemory:              *memory.NewVarMemory(),
		PropMemory:             *memory.NewPropMemory(),
		FnMemory:               *memory.NewFnMemory(),
		AliasMemory:            *memory.NewAliasMemory(),
		InstantiatedFactMemory: *memory.NewInstantiatedFactMemory(),
		UniversalFactMemory:    *memory.NewUniversalFactMemory(),
		VarTypeMemory:          *memory.NewFcVarTypeMemory(),
	}
}

func (env *Env) isNameUsed(name string) (bool, error) {
	if _, ok := parser.Keywords[name]; ok {
		return true, fmt.Errorf("%v is a reserved keyword", name)
	}

	if _, ok := parser.BuiltinSyms[name]; ok {
		return true, fmt.Errorf("%v is a reserved symbol", name)
	}

	if _, got := env.VarMemory.Get(name); got {
		return true, fmt.Errorf("%v is already defined", name)
	}

	if _, got := env.FnMemory.Get(name); got {
		return true, fmt.Errorf("%v is already defined", name)
	}

	if _, got := env.PropMemory.Get(name); got {
		return true, fmt.Errorf("%v is already defined", name)
	}

	if _, got := env.AliasMemory.Get(name); got {
		return true, fmt.Errorf("%v is already defined", name)
	}

	if _, got := pack.ImportedPackDict.Get(name); got {
		return true, fmt.Errorf("%v is already imported", name)
	}

	return false, nil
}

func (e *Env) isVarDefined(name string) bool {
	_, ok := e.VarMemory.Get(name)
	if ok {
		return true
	} else {
		if e.Parent != nil {
			return e.Parent.isVarDefined(name)
		}
		return false
	}
}

func (e *Env) NewVar(pair *parser.FcVarDeclPair) error {
	if e.isVarDefined(pair.Var) {
		return fmt.Errorf("%v is defined", pair.Var)
	}

	_, err := e.VarMemory.Set(pair)
	return err
}
