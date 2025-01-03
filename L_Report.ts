import type { L_Env } from "./L_Env";
import { L_Out, L_Symbol } from "./L_Structs";
import { L_Node, OptFactNode, L_FactNode } from "./L_Nodes";
import { L_Tokens } from "./L_Lexer";
import { Skipper } from "./L_Parser";

function reportFailedFunc(func: Function): string {
  return `<${func.name}> Failed`;
}

export function reportL_Out(env: L_Env, out: L_Out, node: L_Node): L_Out {
  let message = "";

  if (out === L_Out.True) {
    message = `<True> ${node}`;
  } else if (out === L_Out.Unknown) {
    message = `<Unknown> ${node}`;
  } else if (out === L_Out.Error) {
    message = `<Error> ${node}`;
  } else if (out === L_Out.False) {
    message = `<False> ${node}`;
  } else {
    message = `???`;
  }

  return env.report(message);
}

export function lstLengthNotEql(
  env: L_Env,
  lst1: unknown[],
  lst2: unknown[]
): L_Out {
  env.report(
    `Error: ${lst1} and ${lst2} are supposed to have the same length.`
  );

  return L_Out.Error;
}

export function reportNotAllFactsInGivenFactAreDeclared(
  env: L_Env,
  fact: L_FactNode
): L_Out {
  env.report(`Error! Not all of facts in ${fact} are declared`);
  return L_Out.Error;
}

export function reportNewVars(env: L_Env, vars: string[]): L_Out {
  env.report(`[new var] ${vars}`);
  return L_Out.True;
}

export function reportNewExist(env: L_Env, exist: OptFactNode): L_Out {
  env.report(`[new exist] ${exist}`);
  return L_Out.True;
}

export function reportStoreErr(
  env: L_Env,
  funcName: string,
  fact: L_FactNode
): void {
  reportFailedFunctionName(env, funcName);
  env.report(`Failed to store ${fact}`);
}

// export function reportCheckErr(
//   env: L_Env,
//   funcName: string,
//   fact: L_FactNode
// ): void {
//   reportFailedFunctionName(env, funcName);
//   env.errMesReturnL_Out(`[Error] Failed to check ${fact}`);
// }

export function reportFailedFunctionName(
  env: L_Env,
  funcName: string
): boolean {
  env.report(`<${funcName}> Failed`);
  return false;
}

export function L_ReportErr(
  env: L_Env,
  func: Function,
  node?: L_Node | string,
  err?: unknown
): L_Out {
  env.report(`\n<${func.name}> Failed`);
  if (err instanceof Error) env.report(err.message);
  if (node !== undefined) env.report(`Failed: ${node}`);
  return L_Out.Error;
}

export function L_ReportCheckErr(
  env: L_Env,
  func: Function,
  node?: L_Node | string
): L_Out {
  env.report(`[check failed] <${func.name}> Failed`);
  if (node !== undefined) env.report(`Failed: ${node}`);
  return L_Out.Error;
}

export function L_ReportBoolErr(
  env: L_Env,
  func: Function,
  node?: L_Node | string
): boolean {
  env.report(`<${func.name}> Failed`);
  if (node !== undefined) env.report(`${node}`);

  return false;
}

export function L_ReportParserErr(
  env: L_Env,
  tokens: L_Tokens,
  func: Function,
  skipper: Skipper,
  error?: unknown
) {
  // L_ReportErr(env, func, "Parser Error");
  if (error instanceof Error) env.report(error.message);
  env.report(reportFailedFunc(func));
  // env.report(`Error occur at ${tokens.curTokIndex()} ${tokens.peek()}:\n`);
  // env.report(tokens.viewCurTokSurroundings());
  // env.report(`\n${skipperTokens.join(" ")}`);
  // env.report(`At ${tokens.curTokIndex()} ${tokens.peek()}: Parser Error`);
}

export function L_VarsInOptNotDeclaredBool(
  env: L_Env,
  func: Function,
  node: L_FactNode | L_Symbol,
  error?: unknown
): boolean {
  if (error instanceof Error) {
    env.report(error.message);
  }

  if (node instanceof L_FactNode)
    return L_ReportBoolErr(
      env,
      func,
      `At least one parameters in ${node} is not declared. Please check it.`
    );
  else if (node instanceof L_Symbol)
    return L_ReportBoolErr(env, func, `${node} is not declared.`);

  return false;
}

export function L_VarsInOptDoubleDeclErr(
  env: L_Env,
  func: Function,
  symbol: L_Symbol
): boolean {
  return L_ReportBoolErr(env, func, `[Error] ${symbol} already declared.`);
}

export function messageVarNotDeclared(varNotDeclared: string): string {
  return `Not Declared: ${varNotDeclared}`;
}

export function messageParsingError(func: Function, err: unknown): void {
  const out = `Parser Error: Invalid call of ${func.name}.\n`;
  if (err instanceof Error) err.message = out + err.message;
}

// export function messageVarInFactNotDecl()
