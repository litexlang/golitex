import { result } from "lodash";
import { LiTeXNode } from "./ast";
import { LiTeXEnv } from "./env";
import { nodeExec, ResultType } from "./executor";
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
  // "infer p(x: infer xx(y) {infer yyy () {}}) {infer q(y) {infer qq (x) {}} }",
  // "know => p(x,y):pp(z) {p1(x)::pp1(z, #), p2(y); p3(x);}",
  // "infer a(x) {set(x);};",
  // "know a(b);",
  // "know a(c);",
  // "a(b);",
  // "infer a(x) {infer b(y) {set(x,y);} }",
  // "infer a(x: infer p(y: set(s);) {  infer p2(yy: set(yy);) {}  } ) {}",
  // "set(a)::set(x,y);",
  // "infer a(x) {infer b(y: infer subOfY(x) {}) {p(y,x);}}",
  // "know a(1)::b(3);",
  // "a(1)::b(3);",
  // "a(2)::b(3);",
  // ">(2,1);",
  // `know >(a,1);`,
  // `know >(1,0);`,
  // `infer transitivity_of_inequality(x,y,z: >(x,y), >(y,z);) {
  //   >(x,z);
  // }`,
  // `know transitivity_of_inequality(#,#,#);`,
  // ">(a,1);",
  // "infer p(x) {infer q(y) {} } ",
  // "infer a(x) {infer b(y) {} }",
  // "know <=> p(x)::q(y) a(y)::b(x); ;",
  // "know => p(a)::q(b) {a(b), a(b)::b(a);}; ;",
  // "know <= {a(b), a(b)::b(a);} p(a)::q(b) ;;",
  // "inherit p son(z: set(z);) {ha(z);}",
  // "infer P(x) {}",
  // "inherit P son(x: >(x,0);) {}",
  // "know P(#0);",
  // "P(1);",
  // "is_infer(P);",
  // "is_infer(a);",
  // "is_infer(P);",
  // "is_infer(2);",
  "let (x: set(x););",
  "let (y : set(y););",
  "set(x);",
  "let (x: set(x););",
  "set(x);",
  // "def fun(x: set(x), >(x,0););",
];

function callOptsExecTest() {
  for (const item of codes) {
    const tokens = scan(item);
    const result = LiTeXStmtsParse(env, tokens);
    if (result === null) {
      for (let i = 0; i < env.errors.length; i++) {
        console.log(env.errors[i]);
        console.log("parse error: ___________");
      }
    } else {
      for (let i = 0; i < result.length; i++) {
        const res: ResultType = nodeExec(env, result[i]);
        console.log(resultTypeToString(res));
      }
    }
  }
  env.printCallOptFacts();
  env.printInfers();
}

function resultTypeToString(res: ResultType): string {
  switch (res) {
    case ResultType.Error:
      return "error";
    case ResultType.False:
      return "false";
    case ResultType.True:
      return "true";
    case ResultType.Unknown:
      return "unknown";
  }
}

callOptsExecTest();
