package litex_parser

// 包名的map。我在parse的时候需要清楚现在的报名被import到另外一个包的时候，它的新报名叫什么。本质上应该让这一个field跟着tokenblock，甚至做成global。在项目一开始的时候，我根据项目的config文件，或者按照import的包的方式，或者其他什么方式，来初始化这个map。或许我也应该像go一样，在parse前还有一个更前面的stage，就是建立pkgMap的stage。我先读每个文件的import指令
var PkgManagementMap = map[string]string{}
