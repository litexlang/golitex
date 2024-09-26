import { LiTeXEnv } from "./env";
import { nodeExec, ExecInfo, ResultType } from "./executor";
import { scan } from "./lexer";
import { LiTeXStmtsParse } from "./parser";

const env: LiTeXEnv = new LiTeXEnv();

const codes: string[] = [
  // "// Start from one axiom, get followings",
  // "infer Axiom(x,y: P(x), Q(y);) { Thm1(x,y); Thm2(x,y);}",
  // "know P(#x), Q(#2), Axiom(#ha,#y);",
  // "infer Thm1(x,y: Thm2(x,y);) {Thm3(x,y);}",
  // "Thm1(#0, #1);",
  // "Thm3(#x, #3);",
  // "// declare infer using def =>",
  // "def Axiom(x,y: P(x), Q(y)) => {Thm1(x,y), Thm2(x,y);}",
  // "know P(#x), Q(#2), Axiom(#ha,#y);",
  // "def Thm1(x,y: Thm2(x,y)) => {Thm3(x,y);}",
  // "Thm1(#0, #1);",
  // "Thm3(#x, #3);",
  // "// @ is used as know",
  // ": Axiom(x,y| P(x), Q(y)) => {Thm1(x,y), Thm2(x,y);}",
  // "@ P(#x), Q(#2), Axiom(#ha,#y);",
  // ": Thm1(x,y| Thm2(x,y)) => {Thm3(x,y);}",
  // "Thm1(#0, #1);",
  // "Thm3(#x, #3);",
  "// know and declare at the same time",
  "@: fun(#x,3);",
  "fun(2,1);",
  "fun(3,3);",
  "@: deduce(#x,#y) => { corollary(#y,#x);};",
  "deduce(1,2);",
  "corollary(2,1);",
  "// declare subTemplate in template",
  ": fun(x,y) {: subFun(y)}",
  "@ fun(#x, #y)::fun3(#x);",
  "fun(1,2)::fun3(3);",
];

function callOptsExecTest() {
  console.log("\n----results------\n");
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
        const res: ExecInfo = nodeExec(env, result[i]);
        console.log(resultTypeToString(res.type));
      }
    }
  }
  console.log("");
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
    case ResultType.KnowTrue:
      return "knowTrue";
    case ResultType.DefTrue:
      return "defTrue";
  }

  return "";
}

callOptsExecTest();
