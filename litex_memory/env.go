// 约定：var, fn, prop 名不能冲突，即不能有一个变量是var，同时也是Prop
package litexmemory

import (
	"fmt"
	parser "golitex/litex_parser"
)

type Env struct {
	Parent             *Env
	VarMemory          VarMemory
	PropMemory         PropMemory
	FnMemory           FnMemory
	AliasMemory        AliasMemory
	FuncFactMemory     FuncFactMemory
	RelationFactMemory RelationFactMemory
	CondFactMemory     CondFactMemory
	UniFactMemory      UniFactMemory
	VarTypeMemory      FcVarTypeMemory
}

func NewEnv() *Env {
	env := &Env{
		Parent:        nil,
		VarMemory:     *NewVarMemory(),
		PropMemory:    *NewPropMemory(),
		FnMemory:      *NewFnMemory(),
		AliasMemory:   *NewAliasMemory(),
		UniFactMemory: *NewUniFactMemory(),
		VarTypeMemory: *NewFcVarTypeMemory(),
	}

	env.FuncFactMemory = FuncFactMemory{Mem: *NewRedBlackTree(env, specFuncFactCompare)}
	env.RelationFactMemory = RelationFactMemory{Mem: *NewRedBlackTree(env, specRelationFactCompare)}
	env.CondFactMemory = CondFactMemory{Mem: *NewRedBlackTree(env, CondFactMemoryTreeNodeCompare)}

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
