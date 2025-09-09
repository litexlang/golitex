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

func (ver *Verifier) parasSatisfyFnReq(fcFn *ast.FcFn) (*env.FnInFnTMemItem, bool) { // 返回值是 fn(..) fn(..)ret 或 fn(..) T(..) 中的 fn(..)
	fnHeadChain_AndItSelf := ast.GetFnHeadChain_AndItSelf(fcFn)

	// 从后往前找，直到找到有个 fnHead 被已知在一个 fnInFnTInterface 中
	// 比如 f(a)(b,c)(e,d,f) 我不知道 f(a)(b,c) 是哪个 fn_template 里的，但我发现 f(a) $in T 是知道的。那之后就是按T的返回值去套入b,c，然后再把e,d,f套入T的返回值的返回值
	for i := len(fnHeadChain_AndItSelf) - 2; i >= 0; i-- {
		fnHead := fnHeadChain_AndItSelf[i]
		if fnInFnTMemItem, ok := ver.env.GetLatestFnT_GivenNameIsIn(fnHead.String()); ok {
			return fnInFnTMemItem, true
		}
	}

	return nil, false
}
