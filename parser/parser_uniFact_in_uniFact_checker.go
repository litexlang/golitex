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

func checkUniFactDepth0(uniFact *ast.UniFactStmt) error {
	for _, fact := range uniFact.DomFacts {
		if asUniFact, ok := fact.(*ast.UniFactStmt); ok {
			err := checkUniFactDepth1(asUniFact)
			if err != nil {
				return err
			}
		}
	}

	for _, fact := range uniFact.ThenFacts {
		if asUniFact, ok := fact.(*ast.UniFactStmt); ok {
			err := checkUniFactDepth1(asUniFact)
			if err != nil {
				return err
			}
		}
	}

	return nil
}

func checkUniFactDepth1(uniFact *ast.UniFactStmt) error {
	for _, fact := range uniFact.DomFacts {
		if _, ok := fact.(*ast.UniFactStmt); ok {
			return fmt.Errorf("dom fact cannot be a uni fact")
		}
	}

	for _, fact := range uniFact.ThenFacts {
		if _, ok := fact.(*ast.UniFactStmt); ok {
			return fmt.Errorf("then fact cannot be a uni fact")
		}
	}

	return nil
}
