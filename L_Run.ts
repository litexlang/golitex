import { L_Env } from "./L_Env.ts";
import { RType } from "./L_Executor.ts";
import * as L_Executor from "./L_Executor.ts";
import { L_Scan } from "./L_Lexer.ts";
import * as L_Parser from "./L_Parser.ts";

export function runString(env: L_Env, expr: string) {
  try {
    console.log(`-----\n***  source code  ***\n${expr}\n`);
    const tokens = L_Scan(expr);
    const nodes = L_Parser.parseUntilGivenEnd(env, tokens, null);
    if (nodes === undefined) {
      throw Error();
    }
    const result: RType[] = [];
    for (const node of nodes) {
      const out = L_Executor.nodeExec(env, node);
      result.push(out);
    }
    console.log("***  results  ***\n");
    env.printClearMessage();
    console.log();

    return result;
  } catch {
    env.printClearMessage();
    return undefined;
  }
}

export function runStrings(env: L_Env, exprs: string[]) {
  for (let i = 0; i < exprs.length; i++) {
    const expr = exprs[i];
    runString(env, expr);
  }

  env.printExists();
}
