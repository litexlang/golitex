package litex_num

import (
	"fmt"
	"strings"
	"testing"
)

func TestExpandExpression(t *testing.T) {
	expr := "3*[x] + [f(x)]*[y/2] + ([x] + [y]) * [z] + 5*[x]"
	fmt.Println("Input:", expr)
	poly := parseAndExpand(expr)

	var parts []string
	for _, t := range poly {
		parts = append(parts, t.String())
	}
	fmt.Println("Expanded:", strings.Join(parts, " + "))

}
