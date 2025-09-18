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

package data_cleaner

import (
	"fmt"
	"testing"
)

func TestDataCleaner(t *testing.T) {
	code := `
claim:
    forall a N:
        a $in N
    prove:
        a $in N

claim:
    forall a, b, c N:
        a + b = c
        =>:
            a + b = c
    prove:
        a + b = c

claim:
    1 = 1
    prove:
        1 $in N

prove:
    1 + 1 = 2
    claim:
        1 + 1 = 2
        prove:
            1 + 1 = 2
	
	`
	cleanDataSlice, err := CleanStmtSlice(code)
	if err != nil {
		t.Errorf("failed to clean data %s\n", code)
	}

	for _, cleanData := range cleanDataSlice {
		fmt.Println("Assumption:")
		fmt.Println(cleanData.Assumptions)
		fmt.Println("Claim Assumption:")
		fmt.Println(cleanData.ClaimData.ClaimAssumption)
		fmt.Println("Claim Result:")
		fmt.Println(cleanData.ClaimData.ClaimResult)
		fmt.Println("Proofs:")
		fmt.Println(cleanData.ClaimData.Proofs)
		fmt.Println("--------------------------------")
	}
}
