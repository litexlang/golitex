// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Litex email: <litexlang@outlook.com>
// Litex website: https://litexlang.com
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_executor

import (
	ast "golitex/ast"
	env "golitex/environment"
	glob "golitex/glob"
)

func notOkExec(state glob.ExecRet, err error) bool {
	if err != nil {
		return true
	}
	if state.IsUnknown() || state.IsErr() {
		return true
	}
	return false
}

func (exec *Executor) NewCommutativeProp(specFact *ast.SpecFactStmt) {
	if _, ok := exec.env.CommutativePropMem[string(specFact.PropName)]; !ok {
		exec.env.CommutativePropMem[string(specFact.PropName)] = env.NewCommutativePropMemItemStruct()
	}

	switch specFact.TypeEnum {
	case ast.TruePure:
		exec.env.CommutativePropMem[string(specFact.PropName)].TruePureIsCommutative = true
	case ast.FalsePure:
		exec.env.CommutativePropMem[string(specFact.PropName)].FalsePureIsCommutative = true
	default:
		panic("not implemented: not commutative prop")
	}
}
