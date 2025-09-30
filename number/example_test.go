package litex_num

import (
	"fmt"
	"testing"
)

func TestExampleCalculations(t *testing.T) {
	// 测试你提到的问题：1 - 0.3
	result1 := SubDecimal("1", "0.3")
	fmt.Printf("1 - 0.3 = %s\n", result1)
	if result1 != "0.7" {
		t.Errorf("Expected 0.7, got %s", result1)
	}

	// 测试其他例子
	result2 := AddDecimal("0.1", "0.2")
	fmt.Printf("0.1 + 0.2 = %s\n", result2)
	if result2 != "0.3" {
		t.Errorf("Expected 0.3, got %s", result2)
	}

	result3 := SubDecimal("0.30", "0.1")
	fmt.Printf("0.30 - 0.1 = %s\n", result3)
	if result3 != "0.2" {
		t.Errorf("Expected 0.2, got %s", result3)
	}

	result4 := MulDecimal("0.1", "0.2")
	fmt.Printf("0.1 * 0.2 = %s\n", result4)
	if result4 != "0.02" {
		t.Errorf("Expected 0.02, got %s", result4)
	}

	// 测试简化小数
	result5 := AddDecimal("0.30", "0.1")
	fmt.Printf("0.30 + 0.1 = %s\n", result5)
	if result5 != "0.4" {
		t.Errorf("Expected 0.4, got %s", result5)
	}
}
