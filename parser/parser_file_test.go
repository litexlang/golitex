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

package litex_parser

import (
	"fmt"
	"os"
	"path/filepath"
	"testing"
)

// TestParseFile 测试解析单个 .lit 文件
// 使用方法：
// 1. 将你想测试的文件路径放在 testFiles 列表中
// 2. 运行 go test -v -run TestParseFile
func TestParseFile(t *testing.T) {
	// 在这里添加你想测试的文件路径
	testFiles := []string{
		"../examples/test_codes/tmp.lit",
		// 添加更多测试文件...
	}

	for _, filePath := range testFiles {
		t.Run(filepath.Base(filePath), func(t *testing.T) {
			// 读取文件内容
			content, err := os.ReadFile(filePath)
			if err != nil {
				t.Fatalf("Failed to read file %s: %v", filePath, err)
			}

			// 解析源代码
			stmts, err := ParseSourceCode(string(content))
			if err != nil {
				t.Fatalf("Failed to parse file %s: %v", filePath, err)
			}

			// 打印解析结果
			t.Logf("✓ Successfully parsed %s", filePath)
			t.Logf("  Total statements: %d", len(stmts))
			for i, stmt := range stmts {
				t.Logf("  [%d] %T", i, stmt)
			}
		})
	}
}

// TestParseFileVerbose 详细显示每个语句的内容
func TestParseFileVerbose(t *testing.T) {
	// 在这里添加你想测试的文件路径
	testFiles := []string{
		"../examples/test_codes/tmp.lit",
	}

	for _, filePath := range testFiles {
		t.Run(filepath.Base(filePath), func(t *testing.T) {
			// 读取文件内容
			content, err := os.ReadFile(filePath)
			if err != nil {
				t.Fatalf("Failed to read file %s: %v", filePath, err)
			}

			t.Logf("\n========== File: %s ==========", filePath)
			t.Logf("Content:\n%s", string(content))
			t.Logf("\n========== Parsing ==========")

			// 解析源代码
			stmts, err := ParseSourceCode(string(content))
			if err != nil {
				t.Fatalf("Failed to parse file %s: %v", filePath, err)
			}

			// 详细打印解析结果
			t.Logf("✓ Successfully parsed")
			t.Logf("Total statements: %d\n", len(stmts))

			for i, stmt := range stmts {
				t.Logf("========== Statement %d ==========", i)
				t.Logf("Type: %T", stmt)
				t.Logf("String: %s", stmt.String())
				t.Logf("Line: %d", stmt.GetLine())
				t.Logf("")
			}
		})
	}
}

// TestParseDirectory 测试解析整个目录下的所有 .lit 文件
func TestParseDirectory(t *testing.T) {
	// 在这里添加你想测试的目录路径
	testDirs := []string{
		"../examples/test_codes/",
		// "../examples/comprehensive_examples/",
		// 添加更多测试目录...
	}

	for _, dir := range testDirs {
		t.Run(filepath.Base(dir), func(t *testing.T) {
			// 读取目录下所有 .lit 文件
			files, err := filepath.Glob(filepath.Join(dir, "*.lit"))
			if err != nil {
				t.Fatalf("Failed to list files in %s: %v", dir, err)
			}

			if len(files) == 0 {
				t.Logf("No .lit files found in %s", dir)
				return
			}

			successCount := 0
			failCount := 0

			for _, filePath := range files {
				// 读取文件内容
				content, err := os.ReadFile(filePath)
				if err != nil {
					t.Logf("✗ %s: Failed to read file: %v", filepath.Base(filePath), err)
					failCount++
					continue
				}

				// 解析源代码
				_, err = ParseSourceCode(string(content))
				if err != nil {
					t.Logf("✗ %s: Parse error: %v", filepath.Base(filePath), err)
					failCount++
					continue
				}

				t.Logf("✓ %s", filepath.Base(filePath))
				successCount++
			}

			t.Logf("\n========== Summary ==========")
			t.Logf("Total files: %d", len(files))
			t.Logf("Success: %d", successCount)
			t.Logf("Failed: %d", failCount)

			if failCount > 0 {
				t.Errorf("%d file(s) failed to parse", failCount)
			}
		})
	}
}

// TestParseQuickCheck 快速检查单个文件能否解析（用于快速调试）
func TestParseQuickCheck(t *testing.T) {
	// 快速测试文件 - 修改这里测试不同的文件
	filePath := "../examples/test_codes/tmp.lit"

	content, err := os.ReadFile(filePath)
	if err != nil {
		t.Fatalf("Failed to read file: %v", err)
	}

	fmt.Printf("\n========== Parsing: %s ==========\n", filePath)
	fmt.Printf("Content:\n%s\n", string(content))
	fmt.Printf("==========================================\n\n")

	stmts, err := ParseSourceCode(string(content))
	if err != nil {
		t.Fatalf("Parse error: %v", err)
	}

	fmt.Printf("✓ Parse successful! Statements: %d\n\n", len(stmts))
	for i, stmt := range stmts {
		fmt.Printf("[%d] %T\n", i, stmt)
	}
}
