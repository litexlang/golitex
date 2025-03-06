// 约定：var, fn, prop 名不能冲突，即不能有一个变量是var，同时也是Prop
package litexmemory

import (
	"fmt"
	parser "golitex/litex_parser"
)

type Env struct {
	Parent *Env

	VarMemory     VarMemory
	PropMemory    PropMemory
	FnMemory      FnMemory
	VarTypeMemory FcVarTypeMemory

	FuncFactMemory     FuncFactMemory
	CondFactMemory     CondFactMemory
	RelationFactMemory RelationFactMemory
	UniFactMemory      UniFactMemory
	EqualMemory        EqualFactMemory
}

func NewEnv(parent *Env) *Env {
	env := &Env{
		Parent: parent,

		VarMemory:     *NewVarMemory(),
		PropMemory:    *NewPropMemory(),
		FnMemory:      *NewFnMemory(),
		VarTypeMemory: *NewFcVarTypeMemory(),

		FuncFactMemory:     FuncFactMemory{Mem: *NewRedBlackTree(specFuncFactCompare)},
		RelationFactMemory: RelationFactMemory{Mem: *NewRedBlackTree(specRelationFactCompare)},
		CondFactMemory:     CondFactMemory{Mem: *NewRedBlackTree(CondFactMemoryTreeNodeCompare)},
		UniFactMemory:      *NewUniFactMemory(),
	}

	return env
}

func (env *Env) NewKnownFact(stmt *parser.KnowStmt) error {
	for _, fact := range stmt.Facts {
		switch f := fact.(type) {
		case *parser.FuncFactStmt:
			if err := env.NewFuncFact(f); err != nil {
				return err
			}
		case *parser.RelationFactStmt:
			if err := env.RelationFactMemory.NewRelationFact(f); err != nil {
				return err
			}
		case *parser.CondFactStmt:
			if err := env.NewCondFact(f); err != nil {
				return err
			}
		default:
			return fmt.Errorf("unknown fact type: %T", fact)
		}
	}
	return nil
}
