package litex_num

import (
	"testing"
)

func TestAddDecimal(t *testing.T) {
	tests := []struct {
		a, b, expected string
	}{
		{"1", "0.3", "1.3"},
		{"0.3", "1", "1.3"},
		{"0.1", "0.2", "0.3"},
		{"0.30", "0.1", "0.4"},
		{"1.5", "2.5", "4"},
		{"0.99", "0.01", "1"},
		{"0", "0.5", "0.5"},
		{"0.5", "0", "0.5"},
	}

	for _, test := range tests {
		result := AddDecimal(test.a, test.b)
		if result != test.expected {
			t.Errorf("AddDecimal(%s, %s) = %s, expected %s", test.a, test.b, result, test.expected)
		}
	}
}

func TestSubDecimal(t *testing.T) {
	tests := []struct {
		a, b, expected string
	}{
		{"1", "0.3", "0.7"},
		{"0.3", "1", "-0.7"},
		{"1.5", "0.5", "1"},
		{"0.5", "1.5", "-1"},
		{"0.30", "0.1", "0.2"},
		{"0.1", "0.30", "-0.2"},
		{"1", "1", "0"},
		{"0.99", "0.01", "0.98"},
		{"0.01", "0.99", "-0.98"},
		{"0", "0.5", "-0.5"},
		{"0.5", "0", "0.5"},
	}

	for _, test := range tests {
		result := SubDecimal(test.a, test.b)
		if result != test.expected {
			t.Errorf("SubDecimal(%s, %s) = %s, expected %s", test.a, test.b, result, test.expected)
		}
	}
}

func TestMulDecimal(t *testing.T) {
	tests := []struct {
		a, b, expected string
	}{
		{"2", "0.5", "1"},
		{"0.5", "2", "1"},
		{"0.1", "0.2", "0.02"},
		{"0.30", "2", "0.6"},
		{"1.5", "2", "3"},
		{"0.99", "0.01", "0.0099"},
		{"0", "0.5", "0"},
		{"0.5", "0", "0"},
	}

	for _, test := range tests {
		result := MulDecimal(test.a, test.b)
		if result != test.expected {
			t.Errorf("MulDecimal(%s, %s) = %s, expected %s", test.a, test.b, result, test.expected)
		}
	}
}

func TestStripDecimal(t *testing.T) {
	tests := []struct {
		input, expected string
	}{
		{"1.30", "1.3"},
		{"1.00", "1"},
		{"0.30", "0.3"},
		{"0.00", "0"},
		{"1", "1"},
		{"0", "0"},
		{"1.123000", "1.123"},
	}

	for _, test := range tests {
		result := stripDecimal(test.input)
		if result != test.expected {
			t.Errorf("stripDecimal(%s) = %s, expected %s", test.input, result, test.expected)
		}
	}
}
