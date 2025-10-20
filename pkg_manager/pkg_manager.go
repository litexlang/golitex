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
)

// PackageManager handles package operations for Litex
type PackageManager struct {
	// TODO: Add fields for package management
	packages map[string]*Package
}

// Package represents a Litex package
type Package struct {
	Name    string
	Version string
	Path    string
	// TODO: Add more fields as needed
}

// NewPackageManager creates a new package manager instance
func NewPackageManager() *PackageManager {
	return &PackageManager{
		packages: make(map[string]*Package),
	}
}

// RegisterPackage registers a package with the manager
func (pm *PackageManager) RegisterPackage(name, version, path string) error {
	if name == "" {
		return fmt.Errorf("package name cannot be empty")
	}

	pkg := &Package{
		Name:    name,
		Version: version,
		Path:    path,
	}

	pm.packages[name] = pkg
	return nil
}

// GetPackage retrieves a package by name
func (pm *PackageManager) GetPackage(name string) (*Package, bool) {
	pkg, exists := pm.packages[name]
	return pkg, exists
}

// ListPackages returns all registered packages
func (pm *PackageManager) ListPackages() []*Package {
	packages := make([]*Package, 0, len(pm.packages))
	for _, pkg := range pm.packages {
		packages = append(packages, pkg)
	}
	return packages
}
