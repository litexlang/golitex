import { readFileSync } from "fs";
import { scan } from "./lexer";
import { LiTeXEnv } from "./env";
import { LiTeXParse } from "./parser";

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
  // `know
  // def axiom2(a) {
  //   know def fck()  {
  //     know exist S(s: set(s), in(a,s), know def p(x:in(x,s)) {=(x,a)})
  //   };
  // };
  // `,
  "know exist S(s: set(s));",
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
    const result = LiTeXParse(env, tokens);
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
