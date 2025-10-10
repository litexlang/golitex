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

package litex_global

const VERSION = "0.1.11-beta"

const Scope4Indents string = "    "
const EmptyPkg string = ""
const MultiLinesCommentSig string = "\""
const MaxNameLen int = 255
const FuncFactPrefix string = "$"
const InlineCommentSig string = "#"
const ContinueExecutionIfExecUnknown bool = false
const TupleFcFnHead string = "()"
const CheckFalse = false

var AssumeImportFilesAreTrue bool = false

const EndOfInlineForall string = ";"

const InnerGenLine uint = 0

const LatexSig string = "##"

const LatexMultiLineSig string = "\"\""

const LitexFileSuffix string = ".lit"

const PkgEntranceFileName string = "main" + LitexFileSuffix
