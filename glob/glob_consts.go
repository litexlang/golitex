// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Contact the development team: <litexlang@outlook.com>
// Visit litexlang.org and https://github.com/litexlang/golitex for more info.

package litex_global

const Scope4Indents string = "    "

// const EmptyPkgName = ""
const BtEmptyPkgName string = ""

// const BuiltinUnaryPkgName = "#"
const MultiLinesCommentSig string = "\"\"\""
const MaxNameLen int = 255

// 加prefix的好处：如果要执行一个uniFact，那可以直接执行，不用担心检查的时候用到同名的外界obj的事实:因为自由变量全是uniParamPrefix开头的，而用户定义的变量没有uniParamPrefix开头
// 在编译时加入prefix的好处：1. 加prefix这个事情是用不到runtime信息的，所以在编译时可以这么干 2. 确实要比运行时方便：运行时很多地方都需要用到prefix，不如在一开始让所有的uniFact全部加上uniParamPrefix，而不是“有的时候用uniParamPrefix，有的时候不用，这样容易错” 3. 用户写 forall 时，能引入和外部世界重名的变量，而不需要担心冲突（虽然本质上用户不应该被鼓励这么干)
// 在match fc in fact of uniFact 和 fc in fact of concrete fact的时候，对fc in fact of uniFact 是否是 uniParams 的判据，不再是它是否在 paramList( 当然，在 paramList 也是一个判据，但这个判据可能不高效)，而是这个atom是否以`开头。
// 综合来看，添加`好处多多，对用户（用户阅读起来更容易），对我开发（让我不需要那么严苛地考虑重名问题），对运行时甚至都有好处
const UniParamPrefix string = "`"
const FuncFactPrefix string = "$"

const BuiltinExist_St_FactExistParamPropParmSep string = ";"

const CommentSig string = "#"

const FactMaxNumInLogicExpr int = 255
const MaxLogicExprStmtIndexesSize int = 255

const RelaPropNamePrefix string = "$"
const RelaFnPrefix string = "\\"

// const VerifyFcSatisfySpecFactParaReq bool = true
const VerifyFcSatisfySpecFactParaReq bool = false

const ProofContinuesWhenUnknown bool = true

const OverloadOptPrefix string = "__"

const KnowSpecFactByDef = true

const ContinueExecutionWhenExecUnknown bool = true

const MaxLogicExprFactsNum int = 5
