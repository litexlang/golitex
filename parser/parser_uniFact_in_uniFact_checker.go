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

func checkFactsUniDepth(facts []ast.FactStmt) error {
	for _, fact := range facts {
		if asUniFact, ok := fact.(*ast.UniFactStmt); ok {
			err := checkUniFactDepth0(asUniFact)
			if err != nil {
				return err
			}
		}
	}

	return nil
}

func checkUniFactDepth0(uniFact *ast.UniFactStmt) error {
	for _, fact := range uniFact.DomFacts {
		if asUniFact, ok := fact.(*ast.UniFactStmt); ok {
			if !checkUniFactDepth1(asUniFact) {
				return fmt.Errorf("too many levels of universal fact in universal fact:\n%s\nthere must be at most two levels of universal fact", uniFact.String())
			}
		}
	}

	for _, fact := range uniFact.ThenFacts {
		if asUniFact, ok := fact.(*ast.UniFactStmt); ok {
			if !checkUniFactDepth1(asUniFact) {
				return fmt.Errorf("too many levels of universal fact in universal fact:\n%s\nthere must be at most two levels of universal fact", uniFact.String())
			}
		}
	}

	return nil
}

func checkUniFactDepth1(uniFact *ast.UniFactStmt) bool {
	for _, fact := range uniFact.DomFacts {
		if _, ok := fact.(*ast.UniFactStmt); ok {
			return false
		}
	}

	for _, fact := range uniFact.ThenFacts {
		if _, ok := fact.(*ast.UniFactStmt); ok {
			return false
		}
	}

	return true
}
