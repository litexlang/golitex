package litexmemory

import (
	"fmt"
)

const (
	RED   = true
	BLACK = false
)

type PropFactTreeNodeKey int

type PropFactTreeNode struct {
	key    PropFactTreeNodeKey
	color  bool
	left   *PropFactTreeNode
	right  *PropFactTreeNode
	parent *PropFactTreeNode
}

type PropFactRedBlackTree struct {
	root *PropFactTreeNode
}

func NewPropFactTreeNode(key PropFactTreeNodeKey, color bool) *PropFactTreeNode {
	return &PropFactTreeNode{
		key:   key,
		color: color,
	}
}

func (t *PropFactRedBlackTree) insert(key PropFactTreeNodeKey) {
	newNode := NewPropFactTreeNode(key, RED)
	if t.root == nil {
		t.root = newNode
	} else {
		t.insertNode(t.root, newNode)
	}
	t.insertFixup(newNode)
}

func (t *PropFactRedBlackTree) insertNode(root, newNode *PropFactTreeNode) {
	if newNode.key < root.key {
		if root.left == nil {
			root.left = newNode
			newNode.parent = root
		} else {
			t.insertNode(root.left, newNode)
		}
	} else {
		if root.right == nil {
			root.right = newNode
			newNode.parent = root
		} else {
			t.insertNode(root.right, newNode)
		}
	}
}

func (t *PropFactRedBlackTree) insertFixup(node *PropFactTreeNode) {
	for node.parent != nil && node.parent.color == RED {
		if node.parent == node.parent.parent.left {
			uncle := node.parent.parent.right
			if uncle != nil && uncle.color == RED {
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
			if uncle != nil && uncle.color == RED {
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
	t.root.color = BLACK
}

func (t *PropFactRedBlackTree) rotateLeft(x *PropFactTreeNode) {
	y := x.right
	x.right = y.left
	if y.left != nil {
		y.left.parent = x
	}
	y.parent = x.parent
	if x.parent == nil {
		t.root = y
	} else if x == x.parent.left {
		x.parent.left = y
	} else {
		x.parent.right = y
	}
	y.left = x
	x.parent = y
}

func (t *PropFactRedBlackTree) rotateRight(x *PropFactTreeNode) {
	y := x.left
	x.left = y.right
	if y.right != nil {
		y.right.parent = x
	}
	y.parent = x.parent
	if x.parent == nil {
		t.root = y
	} else if x == x.parent.right {
		x.parent.right = y
	} else {
		x.parent.left = y
	}
	y.right = x
	x.parent = y
}

func (t *PropFactRedBlackTree) inorderTraversal(node *PropFactTreeNode) {
	if node != nil {
		t.inorderTraversal(node.left)
		fmt.Printf("%d ", node.key)
		t.inorderTraversal(node.right)
	}
}
