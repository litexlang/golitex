// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Contact the development team: <litexlang@outlook.com>
// Visit litexlang.org and https://github.com/litexlang/golitex for more info.

package litex_verifier

import ast "golitex/ast"

// 就像 async func 和 func 在python中被分离开来，我也分离prop和prop_prop
func (ver *Verifier) IsPropProp(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	// TODO
	return false, nil
}

func (ver *Verifier) PropPropFact(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	// TODO	判断一下传入进来的stmt是不是prop prop，就像数学归纳法这种。prop prop的特点是，它是prop，参数列表里也有prop。如果是的话，那就用其他方式来验证
	return false, nil
}
