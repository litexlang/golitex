9.19

1. iff: know iff xx(..) {}; ;
2. onlyif: parse like iff

9.20
还缺了 or ,not
还缺 => <= <=>
还缺 #
根据字面量 自动绑定性质

如何让下面自动化
`know >(a,1);`,
`know >(1,0);`,
`def transitivity_of_inequality(x,y,z: >(x,y), >(y,z);) {
    >(x,z);
  }`,
`know transitivity_of_inequality(#,#,#);`,
需要让上面跑通：方法是如果我是know，那就自动让 () 里的东西让输入进去的东西成立，比如 know transitivity_of_inequality(3,2,1); 这里即使我之前没声明过 >(3,2), >(2,1) ，
