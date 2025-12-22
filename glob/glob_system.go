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

package litex_global

import (
	"fmt"
	"os"
	"path/filepath"
	"runtime"
)

const SystemRootPath = "litex"

// getSystemRootPath returns the system root directory for litexlang packages.
// On Linux/macOS: ~/litexlang/packages
// On Windows: %USERPROFILE%\litexlang\packages
func getSystemRootPath() string {
	if runtime.GOOS == "windows" {
		return filepath.Join(os.Getenv("USERPROFILE"), SystemRootPath)
	}
	return filepath.Join(os.Getenv("HOME"), SystemRootPath)
}

// GetGlobalPkgAbsPath resolves a package path from the system-wide installed packages.
// If the path is not an absolute path, it will first search in core_packages, then in user_packages.
// If the path is already an absolute path, it will be returned as is.
// Returns an error if the package is not found in either location.
func GetGlobalPkgAbsPath(path string) (string, error) {
	if filepath.IsAbs(path) {
		return path, nil
	}

	systemRoot := getSystemRootPath()

	// First, try core_packages
	corePath := filepath.Join(systemRoot, "core_packages", path)
	if info, err := os.Stat(corePath); err == nil && info.IsDir() {
		return corePath, nil
	}

	// Then, try user_packages
	userPath := filepath.Join(systemRoot, "user_packages", path)
	if info, err := os.Stat(userPath); err == nil && info.IsDir() {
		return userPath, nil
	}

	// Package not found in either location
	return "", fmt.Errorf("package not found: %s (searched in core_packages and user_packages)", path)
}
