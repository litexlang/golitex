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
	"encoding/csv"
	"fmt"
	"os"
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

func TestRead_CSV_OutputCleanData(t *testing.T) {
	fileSlices := []string{
		"../past_examples/minif2f.csv",
		"../past_examples/basic_math1.csv",
		"../past_examples/basic_math2.csv",
		"../past_examples/gsm.csv",
	}

	for _, filePath := range fileSlices {
		// 把filePath的文件名改成cleaned_data.csv
		store_to := filePath[:len(filePath)-4] + "_cleaned_data.csv"
		store_file, err := os.Create(store_to)
		if err != nil {
			t.Errorf("failed to create file %s\n", store_to)
		}
		defer store_file.Close()
		file, err := os.Open(filePath)
		if err != nil {
			t.Errorf("failed to open file %s\n", filePath)
		}
		defer file.Close()

		reader := csv.NewReader(file)
		records, err := reader.ReadAll()
		if err != nil {
			t.Errorf("failed to read csv file %s\n", filePath)
		}

		for _, record := range records {
			code := record[2]
			cleanDataSlice, err := CleanStmtSlice(code)
			if err != nil {
				t.Errorf("failed to clean data %s\n", code)
			}
			if len(cleanDataSlice) == 0 {
				continue
			}

			cleanData := cleanDataSlice[len(cleanDataSlice)-1]

			// 把这一行写入：record[0], record[1], record[2], cleanData.Assumptions, cleanData.ClaimData.ClaimAssumption, cleanData.ClaimData.ClaimResult, cleanData.ClaimData.Proofs

			writer := csv.NewWriter(store_file)
			writer.Write([]string{record[0], record[1], record[2], cleanData.Assumptions, cleanData.ClaimData.ClaimAssumption, cleanData.ClaimData.ClaimResult, cleanData.ClaimData.Proofs})
			writer.Flush()
		}
	}
}
