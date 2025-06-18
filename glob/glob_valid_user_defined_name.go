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
// Litex Zulip community: https://litex.zulipchat.com

package litex_global

import (
	"fmt"
)

func IsValidName(name string) error {
	if len(name) == 0 {
		return fmt.Errorf("identifier name cannot be empty")
	}

	// Check for leading symbols
	if IsKeySymbol(name) {
		return fmt.Errorf("identifier name cannot begin with a reserved symbol")
	}

	// Check for reserved keywords
	if IsKeyword(name) {
		return fmt.Errorf("identifier name cannot be a reserved keyword: '%s'", name)
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
