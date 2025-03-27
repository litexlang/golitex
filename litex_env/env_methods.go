package litexmemory

import (
	"fmt"
	mem "golitex/litex_memory"
	parser "golitex/litex_parser"
)

func (env *Env) NewFact(stmt parser.FactStmt) error {
	switch f := stmt.(type) {
	case *parser.FuncFactStmt:
		return env.NewFuncFact(f)
	case *parser.RelaFactStmt:
		return env.NewRelaFact(f)
	case *parser.CondFactStmt:
		return env.NewCondFact(f)
	default:
		return fmt.Errorf("unknown fact type: %T", stmt)
	}
}

func (env *Env) NewFuncFact(fact *parser.FuncFactStmt) error {
	err := env.FuncFactMem.Insert(fact)
	if err != nil {
		return err
	}
	return nil
}

func (env *Env) NewRelaFact(stmt *parser.RelaFactStmt) error {
	if string(stmt.Opt.OptName) == (parser.KeywordEqual) {
		return env.NewEqualFact(stmt)
	}

	panic(fmt.Sprintf("%v not implemented", string(stmt.Opt.OptName)))
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

func (env *Env) NewCondFact(fact *parser.CondFactStmt) error {
	err := env.CondFactMem.Insert(fact)
	if err != nil {
		return err
	}
	return nil
}
