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

package litex_parser

// 包名的map。我在parse的时候需要清楚现在的报名被import到另外一个包的时候，它的新报名叫什么。本质上应该让这一个field跟着tokenblock，甚至做成global。在项目一开始的时候，我根据项目的config文件，或者按照import的包的方式，或者其他什么方式，来初始化这个map。或许我也应该像go一样，在parse前还有一个更前面的stage，就是建立pkgMap的stage。我先读每个文件的import指令
// 之后考虑像env一样，做的更加独立一点，或构建一个数据结构，parser里面含有 parser_env,这个parser_env里有pkgMap，然后parser_env可以作为参数传入parser的各个函数中。即在tokenblock和stmt阶段之间，有个新数据结构，用来存非执行型语句的中间结果。现在先这么搞着再说，反正我暂时也没多进程。
var PkgManagementMap = map[string]string{}
