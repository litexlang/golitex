package litexglobal

import (
	"fmt"
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

	tree := NewRedBlackTree(compare)

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
