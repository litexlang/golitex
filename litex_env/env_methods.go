package litexmemory

import (
	"fmt"
	mem "golitex/litex_memory"
	st "golitex/litex_statements"
)

func (env *Env) NewFact(stmt st.FactStmt) error {
	switch f := stmt.(type) {
	case *st.SpecFactStmt:
		return env.NewSpecFact(f)
	case *st.CondFactStmt:
		return env.NewCondFact(f)
	case *st.UniFactStmt:
		return env.NewUniFact(f)
	default:
		return fmt.Errorf("unknown fact type: %T", stmt)
	}
}

func (env *Env) NewSpecFact(fact *st.SpecFactStmt) error {
	if fact.IsEqualFact() {
		return env.NewEqualFact(fact)
	}

	err := env.SpecFactMem.Insert(fact)
	if err != nil {
		return err
	}
	return nil
}

func (env *Env) NewEqualFact(stmt *st.SpecFactStmt) error {
	left := &mem.EqualFactMemoryTreeNode{
		FcAsKey: stmt.Params[0],
		Values:  &[]st.Fc{stmt.Params[1]},
	}

	right := &mem.EqualFactMemoryTreeNode{
		FcAsKey: stmt.Params[1],
		Values:  &[]st.Fc{stmt.Params[0]},
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
		equalSlice := &[]st.Fc{stmt.Params[0], stmt.Params[1]}
		env.EqualFactMem.Mem.Insert(left)
		env.EqualFactMem.Mem.Insert(right)
		left.Values = equalSlice
		right.Values = equalSlice
	}

	return nil
}

func (env *Env) NewCondFact(fact *st.CondFactStmt) error {
	err := env.CondFactMem.Insert(fact)
	if err != nil {
		return err
	}
	return nil
}

func (env *Env) NewUniFact(fact *st.UniFactStmt) error {
	// return nil
	err := env.UniFactMem.Insert(fact)
	if err != nil {
		return err
	}
	return nil
}

func (env *Env) IsDeclared(name string) bool {
	// TODO: 不允许变量，函数，prop，type，或者任何名冲突
	return false
}

func (env *Env) Declare(stmt st.Stmt, name string) error {
	// TODO: 声明obj，也可能是fn，甚至可能是prop
	return nil
}

func (env *Env) IsSpecFactPropCommutative(fact *st.SpecFactStmt) bool {
	if len(fact.Params) != 2 {
		return false
	}
	return env.isPropCommutative(&fact.PropName)
}

func (env *Env) isPropCommutative(opt st.Fc) bool {
	if st.IsEqualOpt(opt) {
		return true
	}

	// TODO
	_ = opt
	return false
}

func (env *Env) NewDefConProp(stmt *st.DefConPropStmt, pkgName string) error {
	isDeclared := env.IsDeclared(stmt.DefHeader.Name)
	if isDeclared {
		return fmt.Errorf("%s is already declared", stmt.DefHeader.Name)
	}

	return env.PropMem.Insert(stmt, pkgName)
}

func (env *Env) NewDefObj(stmt *st.DefObjStmt, pkgName string) error {
	for _, objName := range stmt.Objs {
		isDeclared := env.IsDeclared(objName)
		if isDeclared {
			return fmt.Errorf("%s is already declared", objName)
		}
	}

	return env.ObjMem.Insert(stmt, pkgName)
}

func (env *Env) NewDefFn(stmt *st.DefConFnStmt, pkgName string) error {
	isDeclared := env.IsDeclared(stmt.DefHeader.Name)
	if isDeclared {
		return fmt.Errorf("%s is already declared", stmt.DefHeader.Name)
	}

	return env.FnMem.Insert(stmt, pkgName)
}
