# Copyright 2024 Jiachen Shen.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
# Contact the development team: <litexlang@outlook.com>
# Visit litexlang.org and https://github.com/litexlang/golitex for more info.

GOOS=windows GOARCH=amd64 go build -o ./binary/windows_litex.exe main.go

GOOS=linux GOARCH=amd64 go build -o ./binary/linux_litex main.go

GOOS=darwin GOARCH=amd64 go build -o ./binary/mac_litex main.go