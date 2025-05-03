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

package litex_env

import (
	"fmt"
)

func duplicateDefMsg(pkgName string, name string, keyword string) error {
	if pkgName == "" {
		return fmt.Errorf("duplicate definition of %s, it is a %s", name, keyword)
	} else {
		return fmt.Errorf("duplicate definition of %s in %s package, it is a %s", name, pkgName, keyword)
	}
}

func (env *Env) String() string {
	// TODO
	return ""
}

func (fact *StoredSpecFact) String() string {
	return fact.Fact.String()
}

// func (fact *StoredCondSpecFact) String() string {
// 	return fact.Fact.String()
// }

func (fact *StoredUniSpecFact) String() string {
	return fact.UniFact.String()
}
