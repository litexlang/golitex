import { scan } from "./lexer";
import { LiTeXEnv } from "./env";
import { LiTeXStmtsParse } from "./parser";

const codes: string[] = [
  // "set(a):set(b);",
  // "infer a(x: infer p(y: set(s);) {  infer p2(yy: set(yy);) {}  } ) {}",
  // "infer a(x: set(x);) {}",
  // "set(a):set(b);",
  // "set(a), set(b);",
  // "infer p(x: string(x);) {}",
  // "know infer p(x: string(x);) {}, set(a);",
  // "infer object(x) {object(x), object2(x);}",
  // "know object(#);",
  // "infer set(x) {}",
  // "infer eql(x,y) {}",
  // "know => eql(x,y) {strEql(x,y);};",
  // "know <= {eql(x,y);} strEql(x,y) ;",
  // "know <=> eql(x,y) strEql(x,y);",
  // "<=> set(a) set2(a);",
  // "infer in(x,s: set(s)) {\
  //   isIn(x,s);\
  // }",
  // `
  // infer isIn(x,s: set(s)) {
  //   in(x,s);
  // }
  // `,
  // `
  // know iff in(x,s) isIn(x,s); ;
  // `,
  // `infer every_set_is_an_object(s: set(s)) {
  //     object(s);
  //   }`,
  // `have (s: set(s)) ;`,
  // "every_set_is_an_object(s) ; ",
  // `infer = (x,y: set(x), set(y), know infer p1(x:in(x,A)) {in(x,B)}) {
  //   know infer p1(x:in(x,A)) {in(x,B)}, infer  p2(x:in(x,B))  {in(x,A);};
  // }`,
  // `have (x,y: set(x), set(y));`,
  // `know =(x,y);`,
  // "p1;",
  // `infer empty_set(s:set(s)) {
  //   know infer p1(x)  {in(x,s);};
  //   iff p1 empty_set(s) ;
  // }
  // `,
  // `have (EMPTY_SET: empty_set(EMPTY_SET) );`,
  // `
  // know onlyif = (x,y){
  //   know infer p3(x: not_in(x,A))  {not_in(x,B)};
  //   know infer p4(x: not_in(x,B))  {not_in(x,A)};
  // }`,
  // "know infer P(s) {};",
  // `know
  // infer axiom2(a) {
  //   know infer fck()  {
  //     know exist S(s: set(s), in(a,s); know infer p(x:in(x,s)) {=(x,a);}; in(a,s););
  //   };
  // };
  // `,
  // `
  // infer subset(A,B: set(A), set(B)) {
  //   know infer p(x:in(x,a)) {in(x,B);};
  // }`,
  // "know subset(A,B);",
  // "know in(x,a);",
  // "know exist S(s: set(s));",
  // `know infer AxiomN(A,P: set(A), isProperty(P)) {
  //     infer Q(s) {
  //       set(s); know infer Prop(x:in(x,A), P(x)) {};
  //     }
  //         know exist S(s: Q(s));
  // };`,
  // `know infer AxiomM(A:set(A)) {
  //   know infer
  //     QQ(x,y,P: in(x,A), isProperty(P)
  //     )
  //     {
  //  know
  //     exist EEE (s: set(s);
  //       know infer HHH(z :in(z,s)) {
  //         know exist ZZZ(x: in(x,A), P(x,z));
  //       };
  //     );
  //   };
  // };`,
  // ` know
  //     exist EEE (s: set(s);
  //       know infer HHH(z :in(z,s)) {
  //         know exist ZZZ(x: in(x,A), P(x,z));
  //       };
  //     );`,
  // `    know exist EEE (x:
  //     in(x,A), or1_not_set(x), or2_set(x);
  //     know infer PP(y:in(y,x)) {not_in(y,A);};
  //   );`,
  // `know infer AxiomX(A: set(A), not_eq(EMPTY_SET, A)) {
  //   know exist EEE (x:
  //     in(x,A), or1_not_set(x), or2_set(x),
  //     know infer PP(y:in(y,x)) {not_in(y,A);};
  //   );
  // };`,
  // "not {set(s);  know infer p(x:set(s)) {} ; infer s(x: set(x)) {}};",
  // "or {set(s); }{know infer p(x:set(s)) {};  infer s(x: set(x)) {};;;;};",
  // "set(s);",
  // "know infer p(x: set(S)) {};",
  // ";;;",
  // "set(s), set(a);",
  // `exist EEE (x: know infer PP(y: in(y,x)){}; ) ;`,
  // `    infer Q(s) {
  //   set(s); know infer Prop(x: in(x,A), P(x)) {};
  // }`,
  // "infer p(x) {}",
  // "inherit p son(z: set(z);) {ha(z);}",
  // "let (x: set(x););",
  // "set(x);",
  // "let (x: asf(x););",
  // "set(x), >(x,0);",
  // "def bundle(x: set(x), >(x,0));",
  // "know fun(#x) => {fun2(#x); };",
  // "def fun(x: set(x)) => {Set(x);}",
  // "@ : func(x) ;",
  // ": fun(x|set(x)) => {set(x);}",
  // "@: fun(#x,#y);",
  // "fun(2,3);",
  // ": fun(x,y) {: fun2(x,y) ; : fun3(y)}",
  // "@ fun(#x, #y):fun3(#x);",
  // "@ fun(#x, #y):fun4(#x);",
  // "fun(1,2):fun3(3);",
  // "// ",
  // ": func(x,y) {? fun2(x,y);  ? fun3(y) => {fun4(x);} }",
  // ": fun(x) {:fun2(x) ; : fun3(x,y) => {set(x,y);} }",
  // ": func(x,y) {? fun2();  ? fun3(y) => {fun4(x);} }",
  // "know_everything func(1,2):fun2();",
  // "!: func5(2 | set(2)) <=> {func(1):subF(2);} ;",
  // "exist existenceOf(x| set(x))",
  // "have existenceOf(y);",
  // "let x: set(x), set2(x);",
  // "def fun(x) {set(x);}",
  // "know set(#a);",
  // "prove fun(#x []):fun2(1,2: set(1), st2(1,2)) { set(#x);}",
  // "know set(a: set(x)):set2(1,2,3):set3(x,y: set(x):set(t));",
  // "exist func(x: set(x));",
  // "have x: fun(x);",
  // "re_def set(x) {}",
  // "exist ObjExist(x: obj(x)); ObjExist(o);",
  // "know set(#A) => {set(#A);};",
];

function testLexer() {
  // const fileContent: string = readFileSync("example_914.txt", "utf-8");
  const fileContent = "set(1,2):setA(3,4);";
  const tokens = scan(fileContent);
  console.log(tokens);
}

function testParser() {
  const env = new LiTeXEnv();
  for (let i = 0; i < codes.length; i++) {
    const tokens = scan(codes[i]);
    const result = LiTeXStmtsParse(env, tokens);
    if (result === null) {
      const maxDepth = env.errorsWithDepth[env.errorsWithDepth.length - 1][1];
      for (let i = env.errorsWithDepth.length - 1; i >= 0; i--) {
        let space = "";
        for (let j = 0; j < maxDepth - env.errorsWithDepth[i][1]; j++) {
          space += "  ";
        }
        console.log(space + env.errorsWithDepth[i][0]);
      }
    } else {
      for (let i = 0; i < result.length; i++) {
        console.log(result[i]);
      }
    }
  }
}

testParser();
// testLexer();
