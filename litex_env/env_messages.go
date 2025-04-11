package litex_memory

import "fmt"

func nameDeclaredMsg(pkgName string, name string, keyword string) error {
	if pkgName == "" {
		return fmt.Errorf("%s already exists in current scope, it is a %s", name, keyword)
	} else {
		return fmt.Errorf("%s already exists in %s package, it is a %s", name, pkgName, keyword)
	}
}
