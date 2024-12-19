import type { L_Env } from "./L_Env";
import { L_Out } from "./L_Structs";
import type { L_Node, OptNode, ToCheckNode } from "./L_Nodes";

export function reportExecL_Out(out: L_Out, node: L_Node): string {
  if (out === L_Out.True) {
    return `<True> ${node}`;
  } else if (out === L_Out.Unknown) {
    return `<Unknown> ${node}`;
  } else if (out === L_Out.Error) {
    return `<Error> ${node}`;
  } else if (out === L_Out.False) {
    return `<False> ${node}`;
  }

  return `???`;
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
  node?: L_Node | string
): L_Out {
  env.report(`<${func.name}> Failed`);
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
  if (node !== undefined) env.report(`Failed: ${node}`);

  return false;
}

export function L_ParseErr(
  env: L_Env,
  tokens: string[],
  func: Function,
  index: number,
  start: string = ""
) {
  L_ReportErr(env, func, "");
  env.report(`At ${start}[${index * -1}]: ${tokens.slice(0, 20).join(" ")}`);
}
