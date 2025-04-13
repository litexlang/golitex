// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen (malloc_realloc_calloc@outlook.com)
// Visit litexlang.org and https://github.com/litexlang/golitex for more information.

package litex_memory

import "fmt"

func nameDeclaredMsg(pkgName string, name string, keyword string) error {
	if pkgName == "" {
		return fmt.Errorf("%s already exists in current scope, it is a %s", name, keyword)
	} else {
		return fmt.Errorf("%s already exists in %s package, it is a %s", name, pkgName, keyword)
	}
}
