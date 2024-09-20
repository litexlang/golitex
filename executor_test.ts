import { result } from "lodash";
import { LiTeXNode } from "./ast";
import { LiTeXEnv } from "./env";
import { nodeExec } from "./executor";
import { scan } from "./lexer";
import { LiTeXStmtsParse } from "./parser";

const env: LiTeXEnv = new LiTeXEnv();

const codes: string[] = [
  // "set(a)::set(b);",
  // "know set(a)::set(b);",
  // "set(a)::set(b);",
  // "set(c)::set(d);",
  // "know set(1);",
  // "set(1), set(2);",
  // "set(1);",
  // "know set(a), set(b);",
  // "set(a);",
  // "set(c);",
  "",
  // "def p(x: def xx(y) {def yyy () {}}) {def q(y) {def qq (x) {}} }",
  // "know => p(x,y):pp(z) {p1(x)::pp1(z, #), p2(y); p3(x);}",
  // "def a(x) {set(x);};",
  // "know a(b);",
  // "know a(c);",
  // "a(b);",
  // "def a(x) {def b(y) {set(x,y);} }",
  // "def a(x: def p(y: set(s);) {  def p2(yy: set(yy);) {}  } ) {}",
  // "set(a)::set(x,y);",
  // "def a(x) {def b(y) {p(y,x);}}",
  // "know a(1)::b(3);",
  // "a(1)::b(3);",
  // "a(2)::b(3);",
  `know >(a,1);`,
  `know >(1,0);`,
  `def transitivity_of_inequality(x,y,z: >(x,y), >(y,z);) {
    >(x,z);
  }`,
  `know transitivity_of_inequality(#,#,#);`,
];

function callOptsExecTest() {
  for (const item of codes) {
    const tokens = scan(item);
    const result = LiTeXStmtsParse(env, tokens);
    if (result === null) {
      for (let i = 0; i < env.errors.length; i++) {
        console.log("parse error: ___________");
        console.log(env.errors[i]);
        console.log("parse error: ___________");
      }
    } else {
      for (let i = 0; i < result.length; i++) {
        const res = nodeExec(env, result[i]);
        console.log(res);
      }
    }
  }
  console.log(env.defs);
  env.printCallOptFacts();
}

callOptsExecTest();
