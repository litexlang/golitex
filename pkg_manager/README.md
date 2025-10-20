# Litex Package Manager

This directory contains the package management system for Litex.

## Structure

- `pkg_manager.go`: Core package manager implementation
- `pkg_executor.go`: Executor functions for package-related statements
- `pkg_resolver.go`: Symbol resolution for package-qualified names (e.g., `pkgName::symbolName`)

## Features

### Package Registration
The package manager keeps track of all registered packages and their metadata.

### Package Execution
Handles execution of package-related statements:
- Import statements
- Package declarations
- Package loading

### Symbol Resolution
Resolves package-qualified symbols:
- `pkgName::symbolName` - symbol from a specific package
- `pkg1::pkg2::symbol` - nested package references

## Usage

```go
// Create a package manager
pm := NewPackageManager()

// Register a package
pm.RegisterPackage("mypackage", "1.0.0", "/path/to/package")

// Create executors
executor := NewPackageExecutor(pm)
resolver := NewPackageResolver(pm)

// Resolve a symbol
pkgName, symbolName, err := resolver.ResolveSymbol("mypackage::myfunction")
```

## TODO

- [ ] Implement import statement execution
- [ ] Implement package loading from file system
- [ ] Add version management
- [ ] Add dependency resolution
- [ ] Integrate with main executor
- [ ] Add caching for loaded packages
- [ ] Add package search paths
- [ ] Implement package namespacing

