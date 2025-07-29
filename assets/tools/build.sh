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

# Create binary directory if it doesn't exist; 如果存在的话，把里面的东西清理了
rm -rf ./binary
mkdir -p ./binary

# Here is version name
VERSION_NAME=$(grep "VERSION =" main.go | awk '{print $4}' | tr -d '"')

# Windows (64-bit only)
GOOS=windows GOARCH=amd64 go build -o ./binary/windows_64_litex_${VERSION_NAME}.exe main.go

# Linux (64-bit only)
GOOS=linux GOARCH=amd64 go build -o ./binary/linux_64_litex_${VERSION_NAME} main.go

# macOS (Intel + Apple Silicon)
GOOS=darwin GOARCH=amd64 go build -o ./binary/macos_64_litex_${VERSION_NAME} main.go  # Intel Macs

chmod -R 755 ./binary

echo "Build completed. Binaries are in the ./binary directory."