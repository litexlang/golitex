// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Litex email: <litexlang@outlook.com>
// Litex website: https://litexlang.com
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

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
		result := AddDecimalStr(test.a, test.b)
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
		result := SubDecimalStr(test.a, test.b)
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
		result := MulDecimalStr(test.a, test.b)
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
