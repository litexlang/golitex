package litexmemory

const (
	RED   = true
	BLACK = false
)

// Node represents a node in the Red-Black Tree
type Node struct {
	key    interface{} // Key can be of any type
	color  bool        // Color of the node (RED or BLACK)
	left   *Node       // Left child
	right  *Node       // Right child
	parent *Node       // Parent node
}

// RedBlackTree represents the Red-Black Tree
type RedBlackTree struct {
	root    *Node                               // Root of the tree
	compare func(a, b interface{}) (int, error) // Comparison function with error
}

// NewRedBlackTree creates a new Red-Black Tree with a custom comparison function
func NewRedBlackTree(compare func(a, b interface{}) (int, error)) *RedBlackTree {
	return &RedBlackTree{
		compare: compare,
	}
}

// NewNode creates a new node with the given key and color
func NewNode(key interface{}, color bool) *Node {
	return &Node{
		key:   key,
		color: color,
	}
}

// Insert inserts a new key into the Red-Black Tree
func (t *RedBlackTree) Insert(key interface{}) error {
	newNode := NewNode(key, RED)
	if t.root == nil {
		t.root = newNode
	} else {
		err := t.insertNode(t.root, newNode)
		if err != nil {
			return err
		}
	}
	return t.insertFixup(newNode)
}

// insertNode inserts a new node into the tree
func (t *RedBlackTree) insertNode(root, newNode *Node) error {
	compareResult, err := t.compare(newNode.key, root.key)
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
func (t *RedBlackTree) insertFixup(node *Node) error {
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
	t.root.color = BLACK
	return nil
}

// rotateLeft performs a left rotation
func (t *RedBlackTree) rotateLeft(x *Node) {
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

// rotateRight performs a right rotation
func (t *RedBlackTree) rotateRight(x *Node) {
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

// InOrderTraversal performs an in order traversal of the tree
func (t *RedBlackTree) InOrderTraversal(node *Node, visit func(key interface{}) error) error {
	if node != nil {
		if err := t.InOrderTraversal(node.left, visit); err != nil {
			return err
		}
		if err := visit(node.key); err != nil {
			return err
		}
		if err := t.InOrderTraversal(node.right, visit); err != nil {
			return err
		}
	}
	return nil
}
