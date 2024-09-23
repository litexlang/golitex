import { readFileSync } from "fs";
import { scan } from "./lexer";
import { LiTeXEnv } from "./env";
import { LiTeXStmtsParse } from "./parser";
import { LiTeXNode } from "./ast";

// ! know should have different kinds of endings
// ! should able to call subset::p(A,B)(x)
//   ! know infer when used as para, there are so many ; needs refactor
// !
const codes: string[] = [
  // "set(a)::set(b);",
  // "infer a(x: infer p(y: set(s);) {  infer p2(yy: set(yy);) {}  } ) {}",
  // "infer a(x: set(x);) {}",
  // "set(a)::set(b);",
  // "set(a), set(b);", //! strange but works
  // "infer p(x: string(x);) {}", //! I think () here is unnecessary. if I abandon it, I no longer have to adopt sophisticated isEnd
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
  "set(x), >(x,0);",
  "def bundle(x: set(x), >(x,0));",
];

function testLexer() {
  // const fileContent: string = readFileSync("example_914.txt", "utf-8");
  const fileContent = "set(1,2)::setA(3,4);";
  const tokens = scan(fileContent);
  console.log(tokens);
}

function testParser() {
  const env = new LiTeXEnv();
  for (let i = 0; i < codes.length; i++) {
    const tokens = scan(codes[i]);
    const result = LiTeXStmtsParse(env, tokens);
    if (result === null) {
      console.log("_____________");
      for (let i = 0; i < env.errors.length; i++) {
        console.log(env.errors[i]);
      }
      console.log("_____________");
    } else {
      for (let i = 0; i < result.length; i++) {
        console.log(result[i]);
      }
    }
  }
}

testParser();
// testLexer();
