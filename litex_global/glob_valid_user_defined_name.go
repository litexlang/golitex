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

package litex_global

import (
	"fmt"
)

// TODO: 太简陋了，需要改进： 1. 不能以数字开头 2. 不能是关键字 3. 不能是内置函数名 4. 不能是内置变量名 5. 不能是内置符号名
func IsValidName(name string) error {
	if len(name) == 0 {
		return fmt.Errorf("name cannot be empty")
	}

	// 检查开头不能是数字
	first := name[0]
	if first >= '0' && first <= '9' {
		return fmt.Errorf("name cannot start with a number (0-9)")
	}

	if len(name) >= 1 && string(name[0]) == UniParamPrefix {
		return fmt.Errorf("name cannot start with %s", UniParamPrefix)
	}

	if len(name) >= 1 && string(name[0]) == BuiltinUnaryPkgName {
		return fmt.Errorf("name cannot start with %s", BuiltinUnaryPkgName)
	}

	// name 开头不能是 exist_
	if len(name) >= ExistPropPrefixLen && string(name[:ExistPropPrefixLen]) == ExistPropPrefix {
		return fmt.Errorf("name cannot start with %s", ExistPropPrefix)
	}

	if IsKeySymbol(name) {
		return fmt.Errorf("name cannot be a keyword")
	}

	if IsKeyword(name) {
		return fmt.Errorf("name cannot be a keyword")
	}

	// 允许所有其他UTF-8字符（包括emoji、各种语言字符等
	// 只需要确保不是空字符串即可（前面已检查）

	// 长度限制（可选）: 根据前人经验，不要让任何东西超过255个字符
	if len(name) > MaxNameLen {
		return fmt.Errorf("name cannot exceed length 255")
	}

	if IsKeyword(name) || IsKeySymbol(name) {
		return fmt.Errorf("name cannot be a keyword")
	}

	return nil
}
