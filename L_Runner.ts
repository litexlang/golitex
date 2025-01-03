import { L_Env } from "./L_Env";
import { L_Out } from "./L_Structs";
import * as L_Executor from "./L_Executor";
import * as L_Parser from "./L_Parser";
import * as fs from "fs";
import { L_Tokens } from "./L_Lexer";

const printEveryThing = true;

export function runString(
  env: L_Env,
  expr: string
  // printResult: boolean = true,
  // printCode: boolean = false
): L_Out[] | undefined {
  try {
    const tokens = new L_Tokens(expr);

    let result: L_Out[] = [];
    const nodes = L_Parser.parseNodes(env, tokens, null);
    if (nodes === undefined) {
      throw Error();
    }
    for (const node of nodes) {
      const out = L_Executor.L_Exec(env, node);
    }

    return result;
  } catch (error) {
    env.printClearMessage();
    if (error instanceof Error) console.log(error.message);
    return undefined;
  }
}

export function runStrings(env: L_Env, exprs: string[]) {
  for (let i = 0; i < exprs.length; i++) {
    const expr = exprs[i];
    runString(env, expr);
  }
}

export function runFileWithLogging(
  env: L_Env,
  fileName: string
): L_Out[] | undefined {
  try {
    let fileContent: string = "";
    fs.writeFileSync(fileName, fileContent, "utf8");
    // const fileContent = Deno.readTextFileSync(fileName);
    console.log(`Running file: ${fileName}\n`);
    const out = runString(env, fileContent);
    console.log(`End Running file: ${fileName}\n`);
    return out;
  } catch (err) {
    if (err instanceof Error) {
      console.error(
        `Error: Unable to read file "${fileName}": ${err.message}\n`
      );
    } else console.error(`Error: Unable to read file ${fileName}\n`);
  }
}
