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

package litex_global

import (
	"fmt"
	"strings"
)

func IsValidUserDefinedNameWithoutPkgName(name string) error {
	if len(name) == 0 {
		return fmt.Errorf("identifier name cannot be empty")
	}

	// Check for leading symbols
	if IsBuiltinKeywordKeySymbolCanBeFcAtomName(name) {
		return fmt.Errorf("identifier name cannot begin with number, or be a builtin keyword or builtin symbol, get: %s", name)
	}

	if _, ok := builtinPropObjNames[name]; ok {
		return fmt.Errorf("identifier name cannot be a builtin name, get: %s", name)
	}

	// Check maximum length constraint
	if len(name) > MaxNameLen {
		return fmt.Errorf("identifier name exceeds maximum length of %d characters", MaxNameLen)
	}

	// todo: For the time being, I assume all names must start with _ or english letter, and later words can only be number, _ or english letter
	if first := name[0]; first == '_' || first >= 'a' && first <= 'z' || first >= 'A' && first <= 'Z' {
		for _, char := range name[1:] {
			if char >= '0' && char <= '9' || char == '_' || char >= 'a' && char <= 'z' || char >= 'A' && char <= 'Z' {
				continue
			}
			return fmt.Errorf("identifier name can only contain numbers, _, or english letters")
		}
	} else {
		return fmt.Errorf("identifier name must start with _ or english letter")
	}

	return nil
}

func IsValidUseDefinedFcAtom(name string) error {
	// 用：：切割，得到PkgName 和 Name
	values := strings.Split(name, KeySymbolColonColon)

	// values 必须满足 IsValidUserDefinedName
	for _, value := range values {
		if err := IsValidUserDefinedNameWithoutPkgName(value); err != nil {
			return err
		}
	}

	// pkgName 必须声明过啦, 前n-1位join起来
	pkgName := strings.Join(values[:len(values)-1], KeySymbolColonColon)
	if _, ok := DeclaredPkgNames[pkgName]; !ok {
		return fmt.Errorf("package %s is not declared", pkgName)
	}

	return nil
}
