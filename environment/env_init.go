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

package litex_env

import kernel_lib "golitex/kernel_lib"

// template of arithmetic operations。用来证明 + $in fn(R, R)R 这样的事实
func (e *Env) Init() {
	e.NewDefProp_BuiltinProp(kernel_lib.LeftIs0RightIsPositivePropDef)
	e.NewDefProp_BuiltinProp(kernel_lib.LeftIsNegativeRightIsIntegerPropDef)

	e.InsertFnInFnTT(kernel_lib.AddAtom, nil, kernel_lib.AddTemplateQ)
	e.InsertFnInFnTT(kernel_lib.AddAtom, nil, kernel_lib.AddTemplateN)
	e.InsertFnInFnTT(kernel_lib.AddAtom, nil, kernel_lib.AddTemplateZ)
	e.InsertFnInFnTT(kernel_lib.AddAtom, nil, kernel_lib.AddTemplateR)

	e.InsertFnInFnTT(kernel_lib.MinusAtom, nil, kernel_lib.MinusTemplateQ)
	e.InsertFnInFnTT(kernel_lib.MinusAtom, nil, kernel_lib.MinusTemplateN)
	e.InsertFnInFnTT(kernel_lib.MinusAtom, nil, kernel_lib.MinusTemplateZ)
	e.InsertFnInFnTT(kernel_lib.MinusAtom, nil, kernel_lib.MinusTemplateR)

	e.InsertFnInFnTT(kernel_lib.StarAtom, nil, kernel_lib.StarTemplateQ)
	e.InsertFnInFnTT(kernel_lib.StarAtom, nil, kernel_lib.StarTemplateN)
	e.InsertFnInFnTT(kernel_lib.StarAtom, nil, kernel_lib.StarTemplateZ)
	e.InsertFnInFnTT(kernel_lib.StarAtom, nil, kernel_lib.StarTemplateR)

	e.InsertFnInFnTT(kernel_lib.SlashAtom, nil, kernel_lib.SlashTemplateQ)
	e.InsertFnInFnTT(kernel_lib.SlashAtom, nil, kernel_lib.SlashTemplateN)
	e.InsertFnInFnTT(kernel_lib.SlashAtom, nil, kernel_lib.SlashTemplateZ)
	e.InsertFnInFnTT(kernel_lib.SlashAtom, nil, kernel_lib.SlashTemplateR)

	e.InsertFnInFnTT(kernel_lib.ModAtom, nil, kernel_lib.ModTemplate)

	e.InsertFnInFnTT(kernel_lib.PowerAtom, nil, kernel_lib.PowerTemplateR)

	e.InsertFnInFnTT(kernel_lib.ProjAtom, nil, kernel_lib.ProjTemplate)
}
