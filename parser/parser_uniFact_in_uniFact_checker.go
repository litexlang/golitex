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
// Litex website: https://litexlang.org
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_parser

import (
	"fmt"
	ast "golitex/ast"
)

func checkFactsUniDepth0(facts []ast.FactStmt) error {
	for _, fact := range facts {
		switch asFact := fact.(type) {
		case *ast.UniFactStmt:
			err := checkUniFactDepth0(asFact)
			if err != nil {
				return err
			}
		}
	}

	return nil
}

func checkFactsUniDepth1(facts []ast.FactStmt) error {
	for _, fact := range facts {
		switch asFact := fact.(type) {
		case *ast.UniFactStmt:
			ok := checkUniFactDepth1(asFact)
			if !ok {
				return fmt.Errorf("too many levels of universal fact in universal fact:\n%s\nthere must be at most two levels of universal fact", asFact.String())
			}
		}
	}

	return nil
}

func checkUniFactDepth0(uniFact *ast.UniFactStmt) error {
	for _, fact := range uniFact.DomFacts {
		switch asFact := fact.(type) {
		case *ast.UniFactStmt:
			if !checkUniFactDepth1(asFact) {
				return fmt.Errorf("too many levels of universal fact in universal fact:\n%s\nthere must be at most two levels of universal fact", uniFact.String())
			}
		}
	}

	for _, fact := range uniFact.ThenFacts {
		switch asFact := fact.(type) {
		case *ast.UniFactStmt:
			if !checkUniFactDepth1(asFact) {
				return fmt.Errorf("too many levels of universal fact in universal fact:\n%s\nthere must be at most two levels of universal fact", uniFact.String())
			}
		}
	}

	return nil
}

func checkUniFactDepth1(uniFact *ast.UniFactStmt) bool {
	for _, fact := range uniFact.DomFacts {
		switch fact.(type) {
		case *ast.UniFactStmt:
			return false
		}
	}

	for _, fact := range uniFact.ThenFacts {
		switch fact.(type) {
		case *ast.UniFactStmt:
			return false
		}
	}

	return true
}
