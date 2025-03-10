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
		EqualMemory:        EqualFactMemory{Mem: *NewRedBlackTree(EqualFactMemoryTreeNodeCompare)},
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
			if err := env.NewRelationFact(f); err != nil {
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

func (env *Env) NewRelationFact(stmt *parser.RelationFactStmt) error {
	if string(stmt.Opt) == (parser.Keywords["="]) {
		return env.NewEqualFact(stmt)
	}

	panic(fmt.Sprintf("%v not implemented", string(stmt.Opt)))
}

func (env *Env) NewEqualFact(stmt *parser.RelationFactStmt) error {
	left := &EqualFactMemoryTreeNode{
		stmt.Vars[0],
		[]*parser.Fc{&stmt.Vars[1]},
	}

	right := &EqualFactMemoryTreeNode{
		stmt.Vars[1],
		[]*parser.Fc{&stmt.Vars[0]},
	}

	leftSearched, err := env.EqualMemory.Mem.Search(left)
	if err != nil {
		return err
	}
	if leftSearched != nil {
		leftSearched.Key.Values = append(leftSearched.Key.Values, &stmt.Vars[1])
	} else {
		env.EqualMemory.Mem.Insert(left)
	}

	rightSearched, err := env.EqualMemory.Mem.Search(right)
	if err != nil {
		return err
	}
	if rightSearched != nil {
		rightSearched.Key.Values = append(rightSearched.Key.Values, &stmt.Vars[0])
	} else {
		env.EqualMemory.Mem.Insert(right)
	}

	return nil
}
