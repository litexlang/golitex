// 约定：var, fn, property 名不能冲突，即不能有一个变量是var，同时也是Property
package litexenv

import (
	"fmt"
	memory "golitex/litexmemory"
	pack "golitex/litexpackage"
	parser "golitex/litexparser"
)

type Env struct {
	parent           *Env
	varMemory        memory.VarMemory
	propertyMemory   memory.PropertyMemory
	fnMemory         memory.FnMemory
	specFactMemory   memory.SpecificFactMemory
	forallFactMemory memory.ForallFactMemory
	aliasMemory      memory.AliasMemory
}

func (env *Env) isNameUsed(name string) (bool, error) {
	if _, ok := parser.Keywords[name]; ok {
		return true, fmt.Errorf("%v is a reserved keyword", name)
	}

	if _, ok := parser.BuiltinSyms[name]; ok {
		return true, fmt.Errorf("%v is a reserved symbol", name)
	}

	if _, got := env.varMemory.Get(name); got {
		return true, fmt.Errorf("%v is already defined", name)
	}

	if _, got := env.fnMemory.Get(name); got {
		return true, fmt.Errorf("%v is already defined", name)
	}

	if _, got := env.propertyMemory.Get(name); got {
		return true, fmt.Errorf("%v is already defined", name)
	}

	if _, got := pack.ImportedPackDict.Get(name); got {
		return true, fmt.Errorf("%v is already imported", name)
	}

	return false, nil
}

func (e *Env) isVarDefined(name string) bool {
	_, ok := e.varMemory.Get(name)
	if ok {
		return true
	} else {
		if e.parent != nil {
			return e.parent.isVarDefined(name)
		}
		return false
	}
}

func (e *Env) NewVar(pair *parser.FcVarDeclPair) error {
	if e.isVarDefined(pair.Var) {
		return fmt.Errorf("%v is defined", pair.Var)
	}

	_, err := e.varMemory.Set(pair)
	return err
}
