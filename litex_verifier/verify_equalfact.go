package litexverifier

import (
	cmp "golitex/litex_comparator"
	env "golitex/litex_env"
	memory "golitex/litex_memory"
	parser "golitex/litex_parser"
)

func (exec *Verifier) verifyEqualFactSpecifically(curEnv *env.Env, stmt *parser.RelationFactStmt) error {
	key := memory.EqualFactMemoryTreeNode{FcAsKey: stmt.Params[0], Values: []*parser.Fc{}}

	// searchedNode, err := SearchInEnv(curEnv, &curEnv.ConcreteEqualMemory.Mem, &key)
	searchedNode, err := curEnv.ConcreteEqualMemory.Mem.Search(&key)

	if err != nil {
		return err
	}

	comp, err := cmp.CmpFc(stmt.Params[0], stmt.Params[1])

	if err != nil {
		return err
	}
	if comp == 0 {
		exec.success("%v is true, verified by %v", stmt, searchedNode.Key)
		return nil
	}

	if searchedNode == nil {
		return nil
	}

	for _, equalFc := range searchedNode.Key.Values {
		comp, err := cmp.CmpFc(stmt.Params[1], *equalFc)
		if err != nil {
			return err
		}
		if comp == 0 {
			exec.success("%v is true, verified by %v", stmt, equalFc)
			return nil
		}
	}

	return nil
}
