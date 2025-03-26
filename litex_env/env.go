package litexmemory

import (
	"fmt"
	cmp "golitex/litex_comparator"
	ds "golitex/litex_data_structure"
	mem "golitex/litex_memory"
	parser "golitex/litex_parser"
)

type Env struct {
	Parent *Env

	ObjMemory  mem.ObjMemory
	PropMemory mem.PropMemory
	FnMemory   mem.FnMemory

	// 这里必须区分Concrete和Generic
	ConcreteFuncFactMemory     mem.FuncFactMemDict
	ConcreteCondFactMemory     mem.ConcreteCondFactMemory
	ConcreteRelationFactMemory mem.ConcreteRelationFactMemory
	ConcreteUniFactMemory      mem.ConcreteUniFactMemory
	ConcreteEqualMemory        mem.ConcreteEqualFactMemory
}

func NewEnv(parent *Env) *Env {
	env := &Env{
		Parent: parent,

		ObjMemory:  *mem.NewObjMemory(),
		PropMemory: *mem.NewPropMemory(),
		FnMemory:   *mem.NewFnMemory(),

		ConcreteFuncFactMemory:     mem.NewConcreteFuncFactMemDict(),
		ConcreteRelationFactMemory: mem.ConcreteRelationFactMemory{},
		ConcreteCondFactMemory:     mem.ConcreteCondFactMemory{},

		// ConcreteFuncFactMemory:     mem.ConcreteFuncFactMemory{Mem: *ds.NewRedBlackTree(cmp.CmpSpecFuncFact)}, // 需要把env包和memory包分离的一个原因就是，这里会引入cmp，而cmp包要用mem的节点，会cyclic
		// ConcreteRelationFactMemory: mem.ConcreteRelationFactMemory{Mem: *ds.NewRedBlackTree(cmp.SpecRelationFactCompare)},
		// ConcreteCondFactMemory:     mem.ConcreteCondFactMemory{Mem: *ds.NewRedBlackTree(cmp.CondFactMemoryTreeNodeCompare)},
		// UniFactMemory:      *NewUniFactMemory(),
		ConcreteUniFactMemory: mem.ConcreteUniFactMemory{},
		ConcreteEqualMemory:   mem.ConcreteEqualFactMemory{Mem: *ds.NewRedBlackTree(cmp.EqualFactMemoryTreeNodeCompare)},
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
	err := env.ConcreteFuncFactMemory.InsertConcreteFuncFact(fact)
	if err != nil {
		return err
	}
	return nil
	// err := env.ConcreteFuncFactMemory.Mem.Insert(fact)
	// if err != nil {
	// 	return err
	// }
	// return nil
}

func (env *Env) NewRelationFact(stmt *parser.RelationFactStmt) error {
	if string(stmt.Opt.Value) == (parser.KeywordEqual) {
		return env.NewEqualFact(stmt)
	}

	panic(fmt.Sprintf("%v not implemented", string(stmt.Opt.Value)))
}

func (env *Env) NewEqualFact(stmt *parser.RelationFactStmt) error {
	left := &mem.EqualFactMemoryTreeNode{
		FcAsKey: stmt.Params[0],
		Values:  []*parser.Fc{&stmt.Params[1]},
	}

	right := &mem.EqualFactMemoryTreeNode{
		FcAsKey: stmt.Params[1],
		Values:  []*parser.Fc{&stmt.Params[0]},
	}

	leftSearched, err := env.ConcreteEqualMemory.Mem.TreeSearch(left)
	if err != nil {
		return err
	}
	if leftSearched != nil {
		leftSearched.Key.Values = append(leftSearched.Key.Values, &stmt.Params[1])
	} else {
		env.ConcreteEqualMemory.Mem.Insert(left)
	}

	// left = right is eql to right = left, so we memorize both left = right and right = left
	rightSearched, err := env.ConcreteEqualMemory.Mem.TreeSearch(right)
	if err != nil {
		return err
	}
	if rightSearched != nil {
		rightSearched.Key.Values = append(rightSearched.Key.Values, &stmt.Params[0])
	} else {
		env.ConcreteEqualMemory.Mem.Insert(right)
	}

	return nil
}

func (env *Env) NewCondFact(fact *parser.ConditionalFactStmt) error {
	panic("not implemented")
	// for _, f := range fact.ThenFacts {
	// node, err := env.ConcreteCondFactMemory.Mem.TreeSearch(&mem.CondFactMemoryNode{ThenFactAsKey: f, CondFacts: []*parser.ConditionalFactStmt{}})
	// if err != nil {
	// 	return err
	// }
	// if node != nil {
	// 	node.Key.CondFacts = append(node.Key.CondFacts, fact)
	// } else {
	// 	err := env.ConcreteCondFactMemory.Mem.Insert(&mem.CondFactMemoryNode{ThenFactAsKey: f, CondFacts: []*parser.ConditionalFactStmt{fact}})
	// 	if err != nil {
	// 		return err
	// 	}
	// }
	// }
	// return nil
}
