import { readFileSync } from "fs";
import { scan } from "./lexer";
import { LiTeXEnv } from "./env";
import { LiTeXStmtsParse } from "./parser";

const codes: string[] = [
  //   "def object(x) {object(x), object2(x)}",
  //   "know object;",
  //   "def set(x) {}",
  //   "def in(x,s: set(s)) {\
  //   isIn(x,s)\
  // }",
  //   `
  // def isIn(x,s: set(s)) {
  //   in(x,s)
  // }
  // `,
  //   `
  // know eql in(x,s) {
  //   isIn(x,s)
  // };
  // `,
  //   `def every_set_is_an_object(s: set(s)) {
  //     object(s)
  //   }`,
  //   `have s: set(s) ;`,
  //   "every_set_is_an_object(s) ; ",
  //   `def = (x,y: set(x), set(y)) {
  //   know def p1(x:in(x,A)) {in(x,B)}, def  p2(x:in(x,B))  {in(x,A)};
  // }`,
  //   `have x,y: set(x), set(y);`,
  // `know =(x,y);`,
  // "p1;",
  // `def empty_set(s:set(s)) {
  //   know def p1(x)  {in(x,s)};
  //   iff p1 empty_set(s) ;
  // }
  // // `,
  // `have EMPTY_SET: empty_set(EMPTY_SET);`,
  //! not should be used like a keyword instead of a prefix
  // `
  // property = (x,y){
  //   know def p3(x: not_in(x,A))  {not_in(x,B)};
  //   know def p4(x: not_in(x,B))  {not_in(x,A)};
  // }`,
  // "know def P(s) {};",
  //! know should have different kinds of endings
  // `know
  // def axiom2(a) {
  //   know def fck()  {
  //     know exist S(s: set(s), in(a,s), know def p(x:in(x,s)) {=(x,a)};, in(a,s));
  //   };
  // };
  // `,
  // "know exist S(s: set(s));",
  //   `
  // def subset(A,B: set(A), set(B)) {
  //   know def p(x:in(x,a)) {in(x,B)};
  // }`,
  // "know subset(A,B);",
  // "know in(x,a);",
  //! should able to call subset::p(A,B)(x)
  // `    def Q(s) {
  //     set(s), know def Prop(x: in(x,A), P(x)) {};
  //   }`,
  // `know def AxiomN(A,P: set(A), isdef(P)) {
  //     def Q(s) {
  //       set(s); know def Prop(x:in(x,A), P(x)) {};
  //     }
  //         know exist S(s: Q(s));
  // };
  //,
  //! know def when used as para, there are so many ; needs refactor
  //   `know def AxiomM(A:set(A)) {
  //   know def QQ(x,y,P: in(x,A), isdef(P), know def PP(y,y2: P(x,y), P(x,y2)) {eq(y,y2);}; ) {
  //     know exist EEE (s: set(s), know def HHH(z :in(z,s)) {
  //       know exist ZZZ(x: in(x,A), P(x,z));
  // };);
  //   };
  // };`,
  //! or
  //   `know def AxiomX(A: set(A), not_eq(EMPTY_SET, A)) {
  //   know exist EEE (x:
  //     in(x,A), or1_not_set(x), or2_set(x),
  //     know def PP(y:in(y,x)) {not_in(y,A);};
  //   );
  // };`,
  "not {set(s); know def p(x:set(s)) {};  def s(x: set(x)) {}}",
];

function testLexer() {
  const fileContent: string = readFileSync("example_914.txt", "utf-8");
  const tokens = scan(fileContent);
  console.log(tokens[tokens.length - 1]);
}

function testParser() {
  const env = new LiTeXEnv();
  for (let i = 0; i < codes.length; i++) {
    const tokens = scan(codes[i]);
    const result = LiTeXStmtsParse(env, tokens);
    if (result === null) {
      for (let i = 0; i < env.errors.length; i++) {
        console.log(env.errors[i]);
      }
    } else {
      console.log(result);
    }
  }
}

testParser();
