// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Visit litexlang.org and https://github.com/litexlang/golitex for more information.

package main

import (
	"fmt"
	litex_sys "golitex/litex_sys"
)

func main() {
	msg, signal, err := litex_sys.RunFile("./litex_code_examples/use_storedUniFact_with_uniFact_as_dom.lix")
	if err != nil {
		fmt.Println(err.Error())
	}
	fmt.Println(msg)
	fmt.Println(signal)
}
