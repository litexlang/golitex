// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen (malloc_realloc_calloc@outlook.com)
// Visit litexlang.org and https://github.com/litexlang/golitex for more information.

package litex_memory

import ast "golitex/litex_ast"

func (fact *StoredSpecFact) String(atom ast.FcAtom) string {
	knownFact := ast.SpecFactStmt{IsTrue: fact.IsTrue, PropName: atom, Params: fact.Params}
	return knownFact.String()
}

func (fact *StoredCondSpecFact) String() string {
	return fact.Fact.String()
}

func (fact *StoredUniSpecFact) String() string {
	return fact.UniFact.String()
}
