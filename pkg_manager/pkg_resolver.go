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

package litex_pkg_manager

import (
	"fmt"
	"strings"
)

// PackageResolver handles package name resolution
type PackageResolver struct {
	packageManager *PackageManager
}

// NewPackageResolver creates a new package resolver
func NewPackageResolver(pm *PackageManager) *PackageResolver {
	return &PackageResolver{
		packageManager: pm,
	}
}

// ResolveSymbol resolves a symbol with package prefix (e.g., "pkgName::symbolName")
func (pr *PackageResolver) ResolveSymbol(fullName string) (pkgName string, symbolName string, err error) {
	if !strings.Contains(fullName, "::") {
		return "", fullName, nil // No package prefix
	}

	parts := strings.Split(fullName, "::")
	if len(parts) != 2 {
		return "", "", fmt.Errorf("invalid package-qualified name: %s", fullName)
	}

	pkgName = parts[0]
	symbolName = parts[1]

	// Verify package exists
	_, exists := pr.packageManager.GetPackage(pkgName)
	if !exists {
		return "", "", fmt.Errorf("package %s not found", pkgName)
	}

	return pkgName, symbolName, nil
}

// IsPackageQualified checks if a symbol name is package-qualified
func (pr *PackageResolver) IsPackageQualified(name string) bool {
	return strings.Contains(name, "::")
}

// GetPackageName extracts package name from a qualified symbol
func (pr *PackageResolver) GetPackageName(qualifiedName string) string {
	if !strings.Contains(qualifiedName, "::") {
		return ""
	}
	parts := strings.Split(qualifiedName, "::")
	return parts[0]
}

// GetSymbolName extracts symbol name from a qualified symbol
func (pr *PackageResolver) GetSymbolName(qualifiedName string) string {
	if !strings.Contains(qualifiedName, "::") {
		return qualifiedName
	}
	parts := strings.Split(qualifiedName, "::")
	if len(parts) >= 2 {
		return parts[1]
	}
	return qualifiedName
}
