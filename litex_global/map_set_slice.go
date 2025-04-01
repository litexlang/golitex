package litexglobal

func MapKeys[K comparable, V any](m map[K]V) []K {
	keys := make([]K, 0, len(m))
	for k := range m {
		keys = append(keys, k)
	}
	return keys
}

// 把传入的slice变成集合
func SlicesEqualUnordered[T comparable](a, b []T) bool {
	if len(a) != len(b) {
		return false
	}

	// 统计 a 中元素的出现次数
	counts := make(map[T]int)
	for _, v := range a {
		counts[v]++
	}

	// 检查 b 中的元素
	for _, v := range b {
		if counts[v] == 0 {
			return false
		}
		counts[v]--
	}

	return true
}
