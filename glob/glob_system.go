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
	"os"
	"path/filepath"
	"runtime"
)

// GetSystemRootPath returns the system root directory for litexlang packages.
// On Linux/macOS: ~/litexlang/packages
// On Windows: %USERPROFILE%\litexlang\packages
func GetSystemRootPath() string {
	if runtime.GOOS == "windows" {
		return filepath.Join(os.Getenv("USERPROFILE"), "litexlang", "packages")
	}
	return filepath.Join(os.Getenv("HOME"), "litexlang", "packages")
}

// ResolvePackagePath resolves a package path. If the path is not an absolute path,
// it will be resolved relative to the system root directory (~/litexlang/packages).
// If the path is already an absolute path, it will be returned as is.
func ResolvePackagePath(path string) string {
	if filepath.IsAbs(path) {
		return path
	}
	return filepath.Join(GetSystemRootPath(), path)
}
