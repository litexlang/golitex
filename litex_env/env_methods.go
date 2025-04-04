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
		Values:  &[]parser.Fc{stmt.Params[1]},
	}

	right := &mem.EqualFactMemoryTreeNode{
		FcAsKey: stmt.Params[1],
		Values:  &[]parser.Fc{stmt.Params[0]},
	}

	leftSearched, err := env.EqualFactMem.Mem.TreeSearch(left)
	if err != nil {
		return err
	}
	rightSearched, err := env.EqualFactMem.Mem.TreeSearch(right)
	if err != nil {
		return err
	}

	if leftSearched != nil && rightSearched != nil {
		if leftSearched == rightSearched {
			return nil
		} else {
			// 合并两个
			*leftSearched.Key.Values = append(*leftSearched.Key.Values, *rightSearched.Key.Values...)
			rightSearched.Key.Values = leftSearched.Key.Values
		}
	} else if leftSearched == nil && rightSearched != nil {
		*rightSearched.Key.Values = append(*rightSearched.Key.Values, stmt.Params[0])
		left.Values = rightSearched.Key.Values
		env.EqualFactMem.Mem.Insert(left) // 让树中有这个key
	} else if leftSearched != nil && rightSearched == nil {
		*leftSearched.Key.Values = append(*leftSearched.Key.Values, stmt.Params[1])
		right.Values = leftSearched.Key.Values
		env.EqualFactMem.Mem.Insert(right)
	} else if leftSearched == nil && rightSearched == nil {
		equalSlice := &[]parser.Fc{stmt.Params[0], stmt.Params[1]}
		env.EqualFactMem.Mem.Insert(left)
		env.EqualFactMem.Mem.Insert(right)
		left.Values = equalSlice
		right.Values = equalSlice
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

func (env *Env) IsSpecFactPropCommutative(fact *parser.SpecFactStmt) bool {
	if len(fact.Params) != 2 {
		return false
	}
	return env.isPropCommutative(&fact.PropName)
}

func (env *Env) isPropCommutative(opt parser.Fc) bool {
	if parser.IsEqualOpt(opt) {
		return true
	}

	// TODO
	_ = opt
	return false
}

func (env *Env) NewDefConProp(stmt *parser.DefConPropStmt, pkgName string) error {
	// TODO 要防止重名
	return env.PropMem.Insert(stmt, pkgName)
}
