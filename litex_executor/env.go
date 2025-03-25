// * obj, fn, prop 名不能冲突，即不能有一个变量是obj，同时也是Prop
package litexexecutor

import (
	"fmt"
	cmp "golitex/litex_comparator"
	mem "golitex/litex_memory"
	parser "golitex/litex_parser"
)

type Env struct {
	Parent *Env

	ObjMemory  mem.ObjMemory
	PropMemory mem.PropMemory
	FnMemory   mem.FnMemory

	FuncFactMemory     mem.FuncFactMemory
	CondFactMemory     mem.CondFactMemory
	RelationFactMemory mem.RelationFactMemory
	UniFactMemory      mem.UniFactMemory
	EqualMemory        mem.EqualFactMemory
}

func NewEnv(parent *Env) *Env {
	env := &Env{
		Parent: parent,

		ObjMemory:  *mem.NewObjMemory(),
		PropMemory: *mem.NewPropMemory(),
		FnMemory:   *mem.NewFnMemory(),

		FuncFactMemory:     mem.FuncFactMemory{Mem: *mem.NewRedBlackTree(cmp.SpecFuncFactCompare)},
		RelationFactMemory: mem.RelationFactMemory{Mem: *mem.NewRedBlackTree(cmp.SpecRelationFactCompare)},
		CondFactMemory:     mem.CondFactMemory{Mem: *mem.NewRedBlackTree(cmp.CondFactMemoryTreeNodeCompare)},
		// UniFactMemory:      *NewUniFactMemory(),
		UniFactMemory: mem.UniFactMemory{Mem: *mem.NewRedBlackTree(cmp.UniFactMemoryTreeNodeCompare)},
		EqualMemory:   mem.EqualFactMemory{Mem: *mem.NewRedBlackTree(cmp.EqualFactMemoryTreeNodeCompare)},
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
		case *parser.ConditionalFactStmt:
			if err := env.NewCondFact(f); err != nil {
				return err
			}
		default:
			return fmt.Errorf("unknown fact type: %T", fact)
		}
	}
	return nil
}

func (env *Env) NewFuncFact(fact *parser.FuncFactStmt) error {
	err := env.FuncFactMemory.Mem.Insert(fact)
	if err != nil {
		return err
	}
	return nil
}

func (env *Env) NewRelationFact(stmt *parser.RelationFactStmt) error {
	if string(stmt.Opt.Value) == (parser.KeywordEqual) {
		return env.NewEqualFact(stmt)
	}

	panic(fmt.Sprintf("%v not implemented", string(stmt.Opt.Value)))
}

func (env *Env) NewEqualFact(stmt *parser.RelationFactStmt) error {
	left := &mem.EqualFactMemoryTreeNode{
		stmt.Params[0],
		[]*parser.Fc{&stmt.Params[1]},
	}

	right := &mem.EqualFactMemoryTreeNode{
		stmt.Params[1],
		[]*parser.Fc{&stmt.Params[0]},
	}

	leftSearched, err := env.EqualMemory.Mem.Search(left)
	if err != nil {
		return err
	}
	if leftSearched != nil {
		leftSearched.Key.Values = append(leftSearched.Key.Values, &stmt.Params[1])
	} else {
		env.EqualMemory.Mem.Insert(left)
	}

	// left = right is eql to right = left, so we memorize both left = right and right = left
	rightSearched, err := env.EqualMemory.Mem.Search(right)
	if err != nil {
		return err
	}
	if rightSearched != nil {
		rightSearched.Key.Values = append(rightSearched.Key.Values, &stmt.Params[0])
	} else {
		env.EqualMemory.Mem.Insert(right)
	}

	return nil
}

func (env *Env) NewCondFact(fact *parser.ConditionalFactStmt) error {
	for _, f := range fact.ThenFacts {
		node, err := env.CondFactMemory.Mem.Search(&mem.CondFactMemoryNode{f, []*parser.ConditionalFactStmt{}})
		if err != nil {
			return err
		}
		if node != nil {
			node.Key.CondFacts = append(node.Key.CondFacts, fact)
		} else {
			err := env.CondFactMemory.Mem.Insert(&mem.CondFactMemoryNode{f, []*parser.ConditionalFactStmt{fact}})
			if err != nil {
				return err
			}
		}
	}
	return nil
}

// func (tree *mem.RedBlackTree[T]) SearchInEnv(env *Env, key T) (*mem.Node[T], error) {
// 	// TODO: even when given key is different as tree key, we might still view them as the same. For example, when we know x = y, and we have $p(x), we now are verifying $p(y). As tree node, $p(x) is different from $p(y), but since x = y they are the same. So $p(y) should also be verified.

// 	return tree.Search(key)
// }
