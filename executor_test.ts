import { L_Env } from "./env";
import { executor, RType, RTypeMap } from "./executor";
import { scan } from "./lexer";
import { parser } from "./parser";
import { testCode } from "./test_code";

export function testListOfCodes(exprs: string[]): RType[] {
  const copied = [...exprs];
  const env = new L_Env();
  const results: RType[] = [];

  for (let i = 0; i < exprs.length; i++) {
    const expr = exprs[i];
    const out = run(env, expr);
    if (out === undefined) {
      env.printClearMessage();
      continue;
    } else {
      results.concat(out);
    }
  }

  env.printFacts();
  env.printClearMessage();

  return results;
}

function run(env: L_Env, expr: string) {
  try {
    const tokens = scan(expr);
    const nodes = parser.L_StmtsParse(env, tokens);
    if (nodes === undefined) {
      return undefined;
    }
    const result = nodes?.map((e) => executor.nodeExec(env, e));
    env.printClearMessage();

    return result;
  } catch (error) {
    return undefined;
  }
}

// testTao and testCode here works like an electric circuit: both the same: test testList, not the same, test SetTheory. Now I only need to change testCode and testTao to
// specify what I wanna test, instead of jumping between files.
// if (testTao !== testCode) testListOfCodes(setTheory);
// else testListOfCodes(testList);
testCode();
