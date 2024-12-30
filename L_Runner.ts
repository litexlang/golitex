import { L_Env } from "./L_Env";
import { L_Out } from "./L_Structs";
import * as L_Executor from "./L_Executor";
import * as L_Parser from "./L_Parser";
import * as fs from "fs";
import { L_Tokens } from "./L_Lexer";

const printEveryThing = true;

export function runStringWithLogging(
  env: L_Env,
  expr: string,
  printResult: boolean = true,
  printCode: boolean = false
): L_Out[] | undefined {
  try {
    if (printResult && printCode) {
      console.log(`-----\n***  source code  ***\n${expr}\n`);
    }
    const tokens = new L_Tokens(expr);

    let result: L_Out[] = [];
    const nodes = L_Parser.parseNodes(env, tokens, null);
    if (nodes === undefined) {
      throw Error();
    }
    for (const node of nodes) {
      const out = L_Executor.L_Exec(env, node);
      if (printEveryThing) {
        if (true) {
          if (printCode) console.log("***  Messages  ***\n");
          env.printClearMessage();
          console.log();
        } else {
          env.clearMessages();
        }
      } else {
        if (out !== L_Out.True) {
          env.printClearMessage();
          console.log();
        } else {
          env.clearMessages();
        }
      }
    }

    if (printCode) console.log();

    return result;
  } catch {
    env.printClearMessage();
    return undefined;
  }
}

export function runStringsWithLogging(
  env: L_Env,
  exprs: string[],
  printResult: boolean = true
) {
  for (let i = 0; i < exprs.length; i++) {
    const expr = exprs[i];
    runStringWithLogging(env, expr, printResult);
  }

  if (printResult) console.log("-----\nDONE!\n");
  // env.printExists();
}

export function runFileWithLogging(
  env: L_Env,
  fileName: string,
  printResult: boolean = true,
  printCode: boolean = false
): L_Out[] | undefined {
  try {
    let fileContent: string = "";
    fs.writeFileSync(fileName, fileContent, "utf8");
    // const fileContent = Deno.readTextFileSync(fileName);
    console.log(`Running file: ${fileName}\n`);
    const out = runStringWithLogging(env, fileContent, printResult, false);
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
