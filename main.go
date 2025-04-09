package main

import (
	"fmt"
	litex_sys "golitex/litex_sys"
)

func main() {
	msg, err := litex_sys.ExecFileReturnString("./litex_code_examples/use_storedUniFact_with_uniFact_as_dom.lix")
	if err != nil {
		fmt.Println(err.Error())
	}
	fmt.Println(msg)
}
