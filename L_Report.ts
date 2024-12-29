import type { L_Env } from "./L_Env";
import { L_Out, L_Symbol } from "./L_Structs";
import { L_Node, OptNode, ToCheckNode } from "./L_Nodes";

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
  fact: ToCheckNode
): L_Out {
  env.report(`Error! Not all of facts in ${fact} are declared`);
  return L_Out.Error;
}

export function reportNewVars(env: L_Env, vars: string[]): L_Out {
  env.report(`[new var] ${vars}`);
  return L_Out.True;
}

export function reportNewExist(env: L_Env, exist: OptNode): L_Out {
  env.report(`[new exist] ${exist}`);
  return L_Out.True;
}

export function reportStoreErr(
  env: L_Env,
  funcName: string,
  fact: ToCheckNode
): boolean {
  reportFailedFunctionName(env, funcName);
  return env.errMesReturnBoolean(`Failed to store ${fact}`);
}

export function reportCheckErr(
  env: L_Env,
  funcName: string,
  fact: ToCheckNode
): L_Out {
  reportFailedFunctionName(env, funcName);
  return env.errMesReturnL_Out(`[Error] Failed to check ${fact}`);
}

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
  env.report(`\nFailed: <${func.name}>`);
  if (node !== undefined) env.report(`\nFailed:\n${node}`);

  return false;
}

export function L_ReportParserErr(
  env: L_Env,
  tokens: string[],
  func: Function,
  skipperTokens: string[]
) {
  L_ReportErr(env, func, "Parser Error:");
  env.report(`\n${skipperTokens.join(" ")}`);
}

export function L_VarsInOptNotDeclaredBool(
  env: L_Env,
  func: Function,
  node: ToCheckNode | L_Symbol
): boolean {
  if (node instanceof ToCheckNode)
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
