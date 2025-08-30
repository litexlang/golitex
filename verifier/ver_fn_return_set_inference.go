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
// Litex website: https://litexlang.org
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_verifier

import (
	ast "golitex/ast"
	env "golitex/environment"
)

func (ver *Verifier) inferFnInFnTInterface_FromRetSet(fcFn *ast.FcFn) (env.FnInFnTInterface, bool) { // 返回值是 fn(..) fn(..)ret 或 fn(..) T(..) 中的 fn(..)
	panic("")
}

func getFnTInterface_RetSet(fnInFnTInterface env.FnInFnTInterface) ast.Fc {
	switch fnInFnTInterface.(type) {
	case *env.FnTInterface_AsFcFn:
		return getFnTInterface_AsFcFn_Ret(fnInFnTInterface.(*env.FnTInterface_AsFcFn))
	case *env.FnTInterface_AsFnTStruct:
		return getFnTInterface_AsFnTStruct_Ret(fnInFnTInterface.(*env.FnTInterface_AsFnTStruct))
	default:
		panic("unexpected type")
	}
}

func getFnTInterface_AsFcFn_Ret(fnInFnTInterface *env.FnTInterface_AsFcFn) ast.Fc {
	return fnInFnTInterface.Params[0]
}

func getFnTInterface_AsFnTStruct_Ret(fnInFnTInterface *env.FnTInterface_AsFnTStruct) ast.Fc {
	return fnInFnTInterface.RetSet
}
