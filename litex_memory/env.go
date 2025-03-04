// 约定：var, fn, prop 名不能冲突，即不能有一个变量是var，同时也是Prop
package litexmemory

import (
	"fmt"
	pack "golitex/litex_package_management"
	parser "golitex/litex_parser"
)

type Env struct {
	Parent         *Env
	VarMemory      VarMemory
	PropMemory     PropMemory
	FnMemory       FnMemory
	AliasMemory    AliasMemory
	SpecFactMemory SpecFactMemory
	CondFactMemory CondFactMemory
	UniFactMemory  UniFactMemory
	VarTypeMemory  FcVarTypeMemory
}

func NewEnv() *Env {
	return &Env{
		Parent:         nil,
		VarMemory:      *NewVarMemory(),
		PropMemory:     *NewPropMemory(),
		FnMemory:       *NewFnMemory(),
		AliasMemory:    *NewAliasMemory(),
		SpecFactMemory: SpecFactMemory{KnownFacts: *NewRedBlackTree(SpecFactCompare)},
		CondFactMemory: CondFactMemory{KnownFacts: *NewRedBlackTree(CondFactMemoryTreeNodeCompare)},
		UniFactMemory:  *NewUniFactMemory(),
		VarTypeMemory:  *NewFcVarTypeMemory(),
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

func (env *Env) isVarDefined(name string) bool {
	_, ok := env.VarMemory.Get(name)
	if ok {
		return true
	} else {
		if env.Parent != nil {
			return env.Parent.isVarDefined(name)
		}
		return false
	}
}

func (env *Env) NewVar(pair *parser.FcVarDeclPair) error {
	if env.isVarDefined(pair.Var) {
		return fmt.Errorf("%v is defined", pair.Var)
	}

	_, err := env.VarMemory.Set(pair)
	return err
}

func (env *Env) NewKnownFact(stmt *parser.KnowStmt) error {
	for _, fact := range stmt.Facts {
		switch f := fact.(type) {
		case *parser.FuncFactStmt:
			if err := env.SpecFactMemory.NewFuncFact(f); err != nil {
				return err
			}
		case *parser.RelationFactStmt:
			if err := env.SpecFactMemory.NewRelationFact(f); err != nil {
				return err
			}
		case *parser.IfFactStmt:
			if err := env.CondFactMemory.NewFact(f); err != nil {
				return err
			}
		default:
			return fmt.Errorf("unknown fact type: %T", fact)
		}
	}
	return nil
}
