package litex_global

func IsValidName(name string) bool {
	if len(name) == 0 {
		return false
	}

	// 检查开头不能是数字
	first := name[0]
	if first >= '0' && first <= '9' {
		return false
	}

	// 检查不能以双下划线开头
	if len(name) >= 2 && name[0] == '_' && name[1] == '_' {
		return false
	}

	// 允许所有其他UTF-8字符（包括emoji、各种语言字符等
	// 只需要确保不是空字符串即可（前面已检查）

	// 长度限制（可选）
	if len(name) > 255 {
		return false
	}

	if IsKeyword(name) || IsKeySymbol(name) {
		return false
	}

	return true
}
