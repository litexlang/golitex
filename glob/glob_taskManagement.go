package litex_global

import "fmt"

// 存储当前的传入的repo的repo名
var TaskDirName string

var CurrentPkg string = ""
var previousPkg string = ""
var DeclaredPkgNames = map[string]struct{}{"": {}}
var ImportState uint = 0 // 之所以uint而不是bool，因为可以import里有import，离开一个import后我不能让它false掉，因为可能还是在某个import里

func ImportStmtInit(newPkg string) error {
	ImportState++

	previousPkg = CurrentPkg
	CurrentPkg = newPkg
	if newPkg != "" {
		// import name should be valid
		err := IsValidUseDefinedFcAtom(newPkg)
		if err != nil {
			return err
		}

		if _, ok := DeclaredPkgNames[newPkg]; !ok {
			DeclaredPkgNames[newPkg] = struct{}{}
		} else {
			return fmt.Errorf("duplicate package name: '%s'", newPkg)
		}
	}
	return nil
}

func ImportStmtEnd() {
	ImportState--

	CurrentPkg = previousPkg
}

func IsImportState() bool {
	return ImportState > 0
}
