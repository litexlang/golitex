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

import (
	"fmt"
)

// func (e *Env) isValidObjName(name string) bool {
// 	if glob.IsValidUserDefinedName(name) != nil {
// 		return false
// 	}

// 	if e.IsFcAtomDeclared(ast.NewFcAtomWithName(name)) {
// 		return false
// 	}

// 	return true
// }

func (e *Env) NewObj(name string) error {
	err := e.IsValidUserDefinedName_NoDuplicate(name)
	if err != nil {
		return fmt.Errorf("invalid name: %s", name)
	}

	err = e.ObjDefMem.insert(name)
	if err != nil {
		return err
	}

	return nil
}
