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
// Litex discord server: https://discord.gg/uvrHM7eS

package litex_global

import (
	"fmt"
)

func IsValidName(name string) error {
	if len(name) == 0 {
		return fmt.Errorf("identifier name cannot be empty")
	}

	// Check for leading digits
	if first := name[0]; first >= '0' && first <= '9' {
		return fmt.Errorf("identifier name cannot begin with a numeric character (0-9)")
	}

	// Check for universal parameter prefix
	// if len(name) >= 1 && strings.HasPrefix(name, UniPrefix) {
	// 	return fmt.Errorf("identifier name cannot begin with universal parameter prefix '%s'", UniPrefix)
	// }

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

	// Final check for keywords and symbols
	if IsKeyword(name) || IsKeySymbol(name) {
		return fmt.Errorf("identifier name cannot be a reserved keyword or symbol")
	}

	return nil
}
