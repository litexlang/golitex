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
	"unicode"
)

func IsValidUserDefinedNameWithoutPkgName(name string) error {
	if len(name) == 0 {
		return fmt.Errorf("identifier name cannot be empty")
	}

	// 不能以__开头,因为__是litex的内部变量名
	if strings.HasPrefix(name, "__") {
		return fmt.Errorf("identifier name cannot start with __")
	}

	// Check maximum length constraint
	if len(name) > MaxNameLen {
		return fmt.Errorf("identifier name exceeds maximum length of %d characters", MaxNameLen)
	}

	// C语言风格的标识符规则：首字符必须是字母或下划线，不能是数字
	// 后续字符可以是字母、数字、下划线或大部分Unicode字符
	runes := []rune(name)
	if len(runes) == 0 {
		return fmt.Errorf("identifier name cannot be empty")
	}

	// 检查首字符：必须是字母或下划线
	first := runes[0]
	if !(unicode.IsLetter(first) || first == '_') {
		// 如果是数字开头，给出更明确的错误信息
		if unicode.IsDigit(first) {
			return fmt.Errorf("identifier name cannot start with a digit")
		}
		return fmt.Errorf("identifier name must start with a letter or underscore")
	}

	// 检查后续字符：允许字母、数字、下划线以及大部分Unicode字符
	// 排除一些不适合做标识符的字符，如空格、控制字符等
	for i, char := range runes[1:] {
		if unicode.IsLetter(char) || unicode.IsDigit(char) || char == '_' {
			continue
		}
		// 允许其他Unicode字符，但排除控制字符和空白字符
		if unicode.IsControl(char) || unicode.IsSpace(char) {
			return fmt.Errorf("identifier name cannot contain control characters or spaces at position %d", i+1)
		}
		// 允许大部分其他Unicode字符（如中文、日文、emoji等）
	}

	// 检查是否与内置关键字或符号冲突（在字符验证之后）
	if IsBuiltinObjOrPropName(name) {
		return fmt.Errorf("identifier name cannot be a builtin keyword or builtin symbol, get: %s", name)
	}

	if _, ok := builtinPropObjNames[name]; ok {
		return fmt.Errorf("identifier name cannot be a builtin name, get: %s", name)
	}

	return nil
}

func IsValidUseDefinedAtomObj(name string) error {
	// 用：：切割，得到PkgName 和 Name
	values := strings.Split(name, PkgNameAtomSeparator)

	if len(values) == 1 {
		return IsValidUserDefinedNameWithoutPkgName(name)
	} else if len(values) == 2 {
		// values 必须满足 IsValidUserDefinedName
		for _, value := range values {
			if err := IsValidUserDefinedNameWithoutPkgName(value); err != nil {
				return err
			}
		}

		return nil
	} else {
		return fmt.Errorf("identifier name cannot have more than one %s", PkgNameAtomSeparator)
	}
}
