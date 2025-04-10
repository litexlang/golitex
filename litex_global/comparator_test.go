package litex_global

import (
	"fmt"
	"testing"
)

func TestFcEval(t *testing.T) {
	// 测试用例
	testCases := []struct {
		a, b, expected string
	}{
		{"123.45", "67.89", "191.34"},
		{"0.1", "0.2", "0.3"},
		{"99999999999999999999.99999999999999999999", "0.00000000000000000001", "100000000000000000000.00000000000000000000"},
		{"1.0000000000000000000000000000000000000001", "2.0000000000000000000000000000000000000002", "3.0000000000000000000000000000000000000003"},
	}

	for _, tc := range testCases {
		result, _, _ := addBigFloat(tc.a, tc.b)
		fmt.Printf("%s + %s = %s (期望: %s) ", tc.a, tc.b, result, tc.expected)
		if CmpBigFloat(result, tc.expected) == 0 {
			fmt.Println("✓")
		} else {
			fmt.Println("✗")
		}
	}

	fmt.Println(CmpBigFloat("1.23", "1.23000"))    // 0
	fmt.Println(CmpBigFloat("1.23", "1.24"))       // -1
	fmt.Println(CmpBigFloat("123.456", "123.456")) // 0
	fmt.Println(CmpBigFloat("123.456", "123.455")) // 1
	fmt.Println(CmpBigFloat("00001.000", "1"))     // 0
	fmt.Println(CmpBigFloat("10.00001", "10"))     // 1
	fmt.Println(CmpBigFloat("9.9999", "10"))       // -1

}
