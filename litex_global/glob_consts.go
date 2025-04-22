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

package litex_global

const Scope4Indents = "    "
const EmptyPkgName = ""
const BuiltinPkgName = ""
const BuiltinUnaryPkgName = "#"
const MultiLinesCommentSig = "\"\"\""
const MaxNameLen = 255

// 加prefix的好处：如果要执行一个uniFact，那可以直接执行，不用担心检查的时候用到同名的外界obj的事实:因为自由变量全是#开头的，而用户定义的变量没有#开头
// 在编译时加入prefix的好处：1. 加prefix这个事情是用不到runtime信息的，所以在编译时可以这么干 2. 确实要比运行时方便：运行时很多地方都需要用到prefix，不如在一开始让所有的uniFact全部加上#，而不是“有的时候用#，有时候不用，这样容易错”
const UniParamPrefix = "*"
const FuncFactPrefix = "$"

const ExistPropPrefix = "exist_"
const ExistPropPrefixLen = len(ExistPropPrefix)
const BuiltinHaveFactExistParamPropParmSep = ""
