package litex_num

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"strings"
)

func SplitToFraction(expr string) (string, string, error) {
	node, err := parser.ParseExpr(expr)
	if err != nil {
		return "", "", nil
	}
	num, den := handleExpr(node)
	return num, den, nil
}

func handleExpr(e ast.Expr) (string, string) {
	switch v := e.(type) {
	case *ast.BinaryExpr:
		xNum, xDen := handleExpr(v.X)
		yNum, yDen := handleExpr(v.Y)
		switch v.Op {
		case token.QUO:
			return fmt.Sprintf("(%s * %s)", xNum, yDen), fmt.Sprintf("(%s * %s)", xDen, yNum)
		case token.MUL:
			return fmt.Sprintf("(%s * %s)", xNum, yNum), fmt.Sprintf("(%s * %s)", xDen, yDen)
		case token.ADD:
			n := fmt.Sprintf("(%s * %s + %s * %s)", xNum, yDen, yNum, xDen)
			d := fmt.Sprintf("(%s * %s)", xDen, yDen)
			return n, d
		case token.SUB:
			n := fmt.Sprintf("(%s * %s - %s * %s)", xNum, yDen, yNum, xDen)
			d := fmt.Sprintf("(%s * %s)", xDen, yDen)
			return n, d
		case token.XOR:
			return fmt.Sprintf("(%s ^ %s)", xNum, yNum), fmt.Sprintf("(%s ^ %s)", xDen, yDen)
		default:
			return fmt.Sprintf("(%s ? %s)", xNum, yNum), "1"
		}
	case *ast.UnaryExpr:
		if v.Op == token.SUB {
			nNum, nDen := handleExpr(v.X)
			return fmt.Sprintf("(-1 * %s)", nNum), nDen
		}
		return handleExpr(v.X)
	case *ast.ParenExpr:
		nNum, nDen := handleExpr(v.X)
		return fmt.Sprintf("(%s)", nNum), fmt.Sprintf("(%s)", nDen)
	case *ast.Ident:
		return v.Name, "1"
	case *ast.BasicLit:
		return v.Value, "1"
	default:
		return fmt.Sprintf("(%s)", exprToString(e)), "1"
	}
}

func exprToString(e ast.Expr) string {
	var sb strings.Builder
	ast.Inspect(e, func(n ast.Node) bool {
		if n == nil {
			return false
		}
		switch v := n.(type) {
		case *ast.BasicLit:
			sb.WriteString(v.Value)
		case *ast.Ident:
			sb.WriteString(v.Name)
		case *ast.BinaryExpr:
			sb.WriteString("(")
			sb.WriteString(exprToString(v.X))
			sb.WriteString(" ")
			sb.WriteString(v.Op.String())
			sb.WriteString(" ")
			sb.WriteString(exprToString(v.Y))
			sb.WriteString(")")
			return false
		}
		return true
	})
	return sb.String()
}
