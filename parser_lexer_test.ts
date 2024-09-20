import { readFileSync } from "fs";
import { scan } from "./lexer";
import { LiTeXEnv } from "./env";
import { LiTeXStmtsParse } from "./parser";
import { LiTeXNode } from "./ast";

// ! know should have different kinds of endings
// ! should able to call subset::p(A,B)(x)
//   ! know def when used as para, there are so many ; needs refactor
// !
const codes: string[] = [
  "def a(x: def p(y: set(s);) {  def p2(yy: set(yy);) {}  } ) {}",
  // "def a(x: set(x);) {}",
  // "set(a)::set(b);",
  // "set(a), set(b);", //! strange but works
  // "def p(x: string(x);) {}", //! I think () here is unnecessary. if I abandon it, I no longer have to adopt sophisticated isEnd
  // "know def p(x: string(x);) {}, set(a);",
  // "def object(x) {object(x), object2(x);}",
  // "know object(#);",
  // "def set(x) {}",
  // "def eql(x,y) {}",
  // "know => eql(x,y) {strEql(x,y);};",
  // "know <= {eql(x,y);} strEql(x,y) ;",
  // "know <=> eql(x,y) strEql(x,y);",
  // "<=> set(a) set2(a);",
  // "def in(x,s: set(s)) {\
  //   isIn(x,s);\
  // }",
  // `
  // def isIn(x,s: set(s)) {
  //   in(x,s);
  // }
  // `,
  // `
  // know iff in(x,s) isIn(x,s); ;
  // `,
  // `def every_set_is_an_object(s: set(s)) {
  //     object(s);
  //   }`,
  // `have (s: set(s)) ;`,
  // "every_set_is_an_object(s) ; ",
  // `def = (x,y: set(x), set(y), know def p1(x:in(x,A)) {in(x,B)}) {
  //   know def p1(x:in(x,A)) {in(x,B)}, def  p2(x:in(x,B))  {in(x,A);};
  // }`,
  // `have (x,y: set(x), set(y));`,
  // `know =(x,y);`,
  // "p1;",
  // `def empty_set(s:set(s)) {
  //   know def p1(x)  {in(x,s);};
  //   iff p1 empty_set(s) ;
  // }
  // `,
  // `have (EMPTY_SET: empty_set(EMPTY_SET) );`,
  // `
  // know onlyif = (x,y){
  //   know def p3(x: not_in(x,A))  {not_in(x,B)};
  //   know def p4(x: not_in(x,B))  {not_in(x,A)};
  // }`,
  // "know def P(s) {};",
  // `know
  // def axiom2(a) {
  //   know def fck()  {
  //     know exist S(s: set(s), in(a,s); know def p(x:in(x,s)) {=(x,a);}; in(a,s););
  //   };
  // };
  // `,
  // `
  // def subset(A,B: set(A), set(B)) {
  //   know def p(x:in(x,a)) {in(x,B);};
  // }`,
  // "know subset(A,B);",
  // "know in(x,a);",
  // "know exist S(s: set(s));",
  // `know def AxiomN(A,P: set(A), isdef(P)) {
  //     def Q(s) {
  //       set(s); know def Prop(x:in(x,A), P(x)) {};
  //     }
  //         know exist S(s: Q(s));
  // };`,
  // `know def AxiomM(A:set(A)) {
  //   know def
  //     QQ(x,y,P: in(x,A), isdef(P)
  //     )
  //     {
  //  know
  //     exist EEE (s: set(s);
  //       know def HHH(z :in(z,s)) {
  //         know exist ZZZ(x: in(x,A), P(x,z));
  //       };
  //     );
  //   };
  // };`,
  // ` know
  //     exist EEE (s: set(s);
  //       know def HHH(z :in(z,s)) {
  //         know exist ZZZ(x: in(x,A), P(x,z));
  //       };
  //     );`,
  // `    know exist EEE (x:
  //     in(x,A), or1_not_set(x), or2_set(x);
  //     know def PP(y:in(y,x)) {not_in(y,A);};
  //   );`,
  // `know def AxiomX(A: set(A), not_eq(EMPTY_SET, A)) {
  //   know exist EEE (x:
  //     in(x,A), or1_not_set(x), or2_set(x),
  //     know def PP(y:in(y,x)) {not_in(y,A);};
  //   );
  // };`,
  // "not {set(s);  know def p(x:set(s)) {} ; def s(x: set(x)) {}};",
  // "or {set(s); }{know def p(x:set(s)) {};  def s(x: set(x)) {};;;;};",
  // "set(s);",
  // "know def p(x: set(S)) {};",
  // ";;;",
  // "set(s), set(a);",
  // `exist EEE (x: know def PP(y: in(y,x)){}; ) ;`,
  // `    def Q(s) {
  //   set(s); know def Prop(x: in(x,A), P(x)) {};
  // }`,
];

function testLexer() {
  // const fileContent: string = readFileSync("example_914.txt", "utf-8");
  const fileContent = "set::setA(1,2)(3,4);";
  const tokens = scan(fileContent);
  console.log(tokens);
}

function testParser() {
  const env = new LiTeXEnv();
  for (let i = 0; i < codes.length; i++) {
    const tokens = scan(codes[i]);
    const result = LiTeXStmtsParse(env, tokens);
    if (result === null) {
      for (let i = 0; i < env.errors.length; i++) {
        console.log("_____________");
        console.log(env.errors[i]);
        console.log("_____________");
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
