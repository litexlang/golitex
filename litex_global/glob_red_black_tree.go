// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Visit litexlang.org and https://github.com/litexlang/golitex for more information.

// Basic red black tree.

package litex_global

const (
	RED   = true
	BLACK = false
)

// Node represents a node in the Red-Black Tree
type Node[T any] struct {
	Key    T        // Key of the node
	color  bool     // Color of the node (RED or BLACK)
	left   *Node[T] // Left child
	right  *Node[T] // Right child
	parent *Node[T] // Parent node
}

// RedBlackTree represents the Red-Black Tree
type RedBlackTree[T any] struct {
	Root    *Node[T]                  // Root of the tree
	compare func(a, b T) (int, error) // Comparison function with error

}

// NewRedBlackTree creates a new Red-Black Tree with a custom comparison function
func NewRedBlackTree[T any](compare func(a, b T) (int, error)) *RedBlackTree[T] {
	return &RedBlackTree[T]{
		compare: compare,
	}
}

// NewNode creates a new node with the given key and color
func NewNode[T any](key T, color bool) *Node[T] {
	return &Node[T]{
		Key:   key,
		color: color,
	}
}

// Insert inserts a new key into the Red-Black Tree
func (t *RedBlackTree[T]) Insert(key T) error {
	newNode := NewNode(key, RED)
	if t.Root == nil {
		t.Root = newNode
	} else {
		err := t.insertNode(t.Root, newNode)
		if err != nil {
			return err
		}
	}
	return t.insertFixup(newNode)
}

// insertNode inserts a new node into the tree
func (t *RedBlackTree[T]) insertNode(root, newNode *Node[T]) error {
	compareResult, err := t.compare(newNode.Key, root.Key)
	if err != nil {
		return err
	}

	if compareResult < 0 {
		if root.left == nil {
			root.left = newNode
			newNode.parent = root
		} else {
			return t.insertNode(root.left, newNode)
		}
	} else {
		if root.right == nil {
			root.right = newNode
			newNode.parent = root
		} else {
			return t.insertNode(root.right, newNode)
		}
	}
	return nil
}

// insertFixup fixes the Red-Black Tree properties after insertion
func (t *RedBlackTree[T]) insertFixup(node *Node[T]) error {
	for node.parent != nil && node.parent.color {
		if node.parent == node.parent.parent.left {
			uncle := node.parent.parent.right
			if uncle != nil && uncle.color {
				node.parent.color = BLACK
				uncle.color = BLACK
				node.parent.parent.color = RED
				node = node.parent.parent
			} else {
				if node == node.parent.right {
					node = node.parent
					t.rotateLeft(node)
				}
				node.parent.color = BLACK
				node.parent.parent.color = RED
				t.rotateRight(node.parent.parent)
			}
		} else {
			uncle := node.parent.parent.left
			if uncle != nil && uncle.color {
				node.parent.color = BLACK
				uncle.color = BLACK
				node.parent.parent.color = RED
				node = node.parent.parent
			} else {
				if node == node.parent.left {
					node = node.parent
					t.rotateRight(node)
				}
				node.parent.color = BLACK
				node.parent.parent.color = RED
				t.rotateLeft(node.parent.parent)
			}
		}
	}
	t.Root.color = BLACK
	return nil
}

// rotateLeft performs a left rotation
func (t *RedBlackTree[T]) rotateLeft(x *Node[T]) {
	y := x.right
	x.right = y.left
	if y.left != nil {
		y.left.parent = x
	}
	y.parent = x.parent
	if x.parent == nil {
		t.Root = y
	} else if x == x.parent.left {
		x.parent.left = y
	} else {
		x.parent.right = y
	}
	y.left = x
	x.parent = y
}

// rotateRight performs a right rotation
func (t *RedBlackTree[T]) rotateRight(x *Node[T]) {
	y := x.left
	x.left = y.right
	if y.right != nil {
		y.right.parent = x
	}
	y.parent = x.parent
	if x.parent == nil {
		t.Root = y
	} else if x == x.parent.right {
		x.parent.right = y
	} else {
		x.parent.left = y
	}
	y.right = x
	x.parent = y
}

// InOrderTraversal performs an in-order traversal of the tree
func (t *RedBlackTree[T]) InOrderTraversal(node *Node[T], visit func(key T) error) error {
	if node != nil {
		if err := t.InOrderTraversal(node.left, visit); err != nil {
			return err
		}
		if err := visit(node.Key); err != nil {
			return err
		}
		if err := t.InOrderTraversal(node.right, visit); err != nil {
			return err
		}
	}
	return nil
}

// TreeSearch searches for a key in the Red-Black Tree and returns the corresponding node if found.
func (t *RedBlackTree[T]) TreeSearch(key T) (*Node[T], error) {
	return t.searchNode(t.Root, key)
}

// searchNode recursively searches for a key in the tree and returns the corresponding node if found.
func (t *RedBlackTree[T]) searchNode(node *Node[T], key T) (*Node[T], error) {
	if node == nil {
		return nil, nil
	}

	compareResult, err := t.compare(key, node.Key)
	if err != nil {
		return nil, err
	}

	if compareResult == 0 {
		return node, nil // 返回找到的节点
	} else if compareResult < 0 {
		return t.searchNode(node.left, key)
	} else {
		return t.searchNode(node.right, key)
	}
}

func (t *RedBlackTree[T]) SearchOneLayer(node *Node[T], key T) (*Node[T], error, bool) {
	if node == nil {
		return nil, nil, false
	}

	compareResult, err := t.compare(key, node.Key)
	if err != nil {
		return nil, err, false
	}

	if compareResult == 0 {
		return node, nil, true // 返回找到的节点, 找到返回true
	} else if compareResult < 0 {
		return node.left, nil, false
	} else {
		return node.right, nil, false
	}
}
