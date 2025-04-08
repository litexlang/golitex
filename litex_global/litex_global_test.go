package litex_global_test

import (
	"fmt"
	glob "golitex/litex_global"
	"testing"
)

func TestRedBlackTree(t *testing.T) {
	// 定义比较函数
	compare := func(a, b int) (int, error) {
		keyA := a
		keyB := b
		if keyA < keyB {
			return -1, nil
		} else if keyA > keyB {
			return 1, nil
		}
		return 0, nil
	}

	tree := glob.NewRedBlackTree(compare)

	// 插入键
	keys := []int{10, 20, 30, 15, 25}
	for _, key := range keys {
		if err := tree.Insert(key); err != nil {
			fmt.Println("Insert error:", err)
			return
		}
	}

	// 中序遍历
	fmt.Println("In-order traversal:")
	tree.InOrderTraversal(tree.Root, func(key int) error {
		fmt.Println(key)
		return nil
	})
}

func TestIsValidName(t *testing.T) {
	tests := []struct {
		name string
		want bool
	}{
		{"变量", true},
		{"αβγ", true},
		{"_name", true},
		{"name123", true},
		{"🍎", true},         // emoji
		{"東京", true},        // 日文
		{"user@name", true}, // 特殊符号（现在允许）
		{"123name", false},  // 数字开头
		{"__secret", false}, // 双下划线开头
		{"", false},         // 空字符串
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if got := glob.IsValidName(tt.name); got != tt.want {
				t.Errorf("IsValidName(%q) = %v, want %v", tt.name, got, tt.want)
			}
		})
	}
}
