package litex_global

import "fmt"

func IsValidName(name string) error {
	if len(name) == 0 {
		return fmt.Errorf("name cannot be empty")
	}

	// 检查开头不能是数字
	first := name[0]
	if first >= '0' && first <= '9' {
		return fmt.Errorf("name cannot start with a number (0-9)")
	}

	// 开头不能以#
	if len(name) >= 1 && string(name[0]) == UniFactParamPrefix {
		return fmt.Errorf("name cannot start with #")
	}

	// 检查不能以双下划线开头
	if len(name) >= 2 && name[0] == '_' && name[1] == '_' {
		return fmt.Errorf("name cannot start with double underscore __")
	}

	// 允许所有其他UTF-8字符（包括emoji、各种语言字符等
	// 只需要确保不是空字符串即可（前面已检查）

	// 长度限制（可选）
	if len(name) > 255 {
		return fmt.Errorf("name cannot exceed length 255")
	}

	if IsKeyword(name) || IsKeySymbol(name) {
		return fmt.Errorf("name cannot be a keyword")
	}

	return nil
}
