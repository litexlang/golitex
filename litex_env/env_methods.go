package litexmemory

import (
	"fmt"
	mem "golitex/litex_memory"
	parser "golitex/litex_parser"
)

func (env *Env) NewFact(stmt parser.FactStmt) error {
	switch f := stmt.(type) {
	case *parser.SpecFactStmt:
		return env.NewSpecFact(f)
	case *parser.CondFactStmt:
		return env.NewCondFact(f)
	case *parser.UniFactStmt:
		return env.NewUniFact(f)
	default:
		return fmt.Errorf("unknown fact type: %T", stmt)
	}
}

func (env *Env) NewSpecFact(fact *parser.SpecFactStmt) error {
	if fact.IsEqualFact() {
		return env.NewEqualFact(fact)
	}

	err := env.SpecFactMem.Insert(fact)
	if err != nil {
		return err
	}
	return nil
}

func (env *Env) NewEqualFact(stmt *parser.SpecFactStmt) error {
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

func (env *Env) NewCondFact(fact *parser.CondFactStmt) error {
	err := env.CondFactMem.Insert(fact)
	if err != nil {
		return err
	}
	return nil
}

func (env *Env) NewUniFact(fact *parser.UniFactStmt) error {
	// return nil
	err := env.UniFactMem.Insert(fact)
	if err != nil {
		return err
	}
	return nil
}

func (env *Env) IsDeclared(name string) (bool, error) {
	// TODO: 不允许变量，函数，prop，type，或者任何名冲突
	return false, nil
}

func (env *Env) Declare(stmt parser.Stmt, name string) error {
	// TODO: 声明obj，也可能是fn，甚至可能是prop
	return nil
}
