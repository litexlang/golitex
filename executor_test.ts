import { LiTeXNode } from "./ast";
import { LiTeXEnv } from "./env";
import { nodeExec } from "./executor";
import { scan } from "./lexer";
import { LiTeXStmtsParse } from "./parser";

const env: LiTeXEnv = new LiTeXEnv();

const codes: string[] = [
  "set(a)::set(b);",
  "know set(a)::set(b);",
  "set(a)::set(b);",
  "set(c)::set(d);",
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
}

callOptsExecTest();
