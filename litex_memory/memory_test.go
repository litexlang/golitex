package litexmemory

import (
	"fmt"
	"testing"
)

func TestRedBlackTree(t *testing.T) {
	// Example usage with string keys
	compareStrings := func(a, b interface{}) int {
		sa := a.(string)
		sb := b.(string)
		if sa < sb {
			return -1
		} else if sa > sb {
			return 1
		}
		return 0
	}

	tree := NewRedBlackTree(compareStrings)
	keys := []string{"apple", "banana", "cherry", "date", "elderberry"}
	for _, key := range keys {
		tree.Insert(key)
	}

	fmt.Println("InOrder Traversal:")
	tree.InOrderTraversal(tree.root, func(key interface{}) {
		fmt.Printf("%s ", key)
	})
	fmt.Println()

}
