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
  // "let (x: set(x););",
  // "let (y : set(y););",
  // "set(x);",
  // "let (x: set(x););",
  // "set(x);",
  // "def fun(x: set(x), >(x,0););",
  // "set(x);",
  // "set(y);",
  // "set(1);",
  // "know set(#);",
  // "set(2);",
  // "infer EVERYTHING_IS_SET (X) {set(X);};", // if X needs extra requirements, you must use infer, know-infer, by-infer instead of #.
  // "know infer EVERYTHING_IS_SET(x);",
  // "by-infer EVERYTHING_IS_SET(2);",
  // "set(2)",
  // "infer IF-ELSE( Q, P: F1(P), F2(Q);) {F1(Q);}",
  // "know F1(P), F2(Q);",
  // "know proof Proof-Of-If-Else(X,Y: F1(X);) => {F1(Q); F3(P);}",
  // emit new facts because forall variables, Proof-Of-If-Else is correct, so a fixed var is also right.
  // "Proof-Of-If-Else(P,Q);", // emit F1(Q), F3(P)
  // "F1(Q);",
  // "by Proof-Of-If-Else(X,Y) => IF-ELSE(Y,X) ;", // here X,Y are both free variables, my interpreter helps to do check (use #)
  // "know HA(#);",
  // "HA(1);",
  // "HA(2);",
  // "know infer HA2(x: >(x,1)) {result(x);}",
  // "HA2(3);", // check is right, emit corollaries of infer
  // "result(3);", // HA2's corollary
  // "def natural_number(x): cond;",
  // "let natural_number(x);",
  // "if-then next_is_right(P: 判断式, n 是自然数) P(n) => P(n+1);",
  // "know next_is_right(P,n);",
  // "proof Prove(x,y: cond(x,y);) => {goal(x,y), goal2(x);} {...; ; }",
  // "by Prove(x,y) => next_is_right()",
  // "or set-or-number x: set(x), number(x);",
  "infer IF-THEN(Q, P: F1(P), F2(Q)) {F1(Q);}",
  "know F1(P), F2(Q);",
  "know IF-THEN(Q,P);",
  "F1(Q);",
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
