package litexmemory

import (
	"fmt"
	mem "golitex/litex_memory"
	parser "golitex/litex_parser"
)

func (env *Env) NewKnownFact(stmt *parser.KnowStmt) error {
	for _, fact := range stmt.Facts {
		switch f := fact.(type) {
		case *parser.FuncFactStmt:
			if err := env.NewFuncFact(f); err != nil {
				return err
			}
		case *parser.RelaFactStmt:
			if err := env.NewRelaFact(f); err != nil {
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
	err := env.FuncFactMem.InsertConcreteFuncFact(fact)
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

func (env *Env) NewRelaFact(stmt *parser.RelaFactStmt) error {
	if string(stmt.Opt.Value) == (parser.KeywordEqual) {
		return env.NewEqualFact(stmt)
	}

	panic(fmt.Sprintf("%v not implemented", string(stmt.Opt.Value)))
}

func (env *Env) NewEqualFact(stmt *parser.RelaFactStmt) error {
	left := &mem.EqualFactMemoryTreeNode{
		FcAsKey: stmt.Params[0],
		Values:  []*parser.Fc{&stmt.Params[1]},
	}

	right := &mem.EqualFactMemoryTreeNode{
		FcAsKey: stmt.Params[1],
		Values:  []*parser.Fc{&stmt.Params[0]},
	}

	leftSearched, err := env.EqualFactMem.Mem.TreeSearch(left)
	if err != nil {
		return err
	}
	if leftSearched != nil {
		leftSearched.Key.Values = append(leftSearched.Key.Values, &stmt.Params[1])
	} else {
		env.EqualFactMem.Mem.Insert(left)
	}

	// left = right is eql to right = left, so we memorize both left = right and right = left
	rightSearched, err := env.EqualFactMem.Mem.TreeSearch(right)
	if err != nil {
		return err
	}
	if rightSearched != nil {
		rightSearched.Key.Values = append(rightSearched.Key.Values, &stmt.Params[0])
	} else {
		env.EqualFactMem.Mem.Insert(right)
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
