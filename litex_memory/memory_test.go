package litexmemory

import (
	"errors"
	"fmt"
	"testing"
)

func TestRedBlackTree(t *testing.T) {
	// 定义比较函数
	compare := func(a, b interface{}) (int, error) {
		keyA, okA := a.(int)
		keyB, okB := b.(int)
		if !okA || !okB {
			return 0, errors.New("invalid key type")
		}
		if keyA < keyB {
			return -1, nil
		} else if keyA > keyB {
			return 1, nil
		}
		return 0, nil
	}

	// 创建红黑树
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
	tree.InOrderTraversal(tree.root, func(key interface{}) error {
		fmt.Println(key)
		return nil
	})
}
