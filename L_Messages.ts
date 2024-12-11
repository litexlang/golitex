import type { L_Env } from "./L_Env";
import { L_Out } from "./L_Structs";
import type { L_Node, OptNode, ToCheckNode } from "./L_Nodes";

export function reportExecL_Out(out: L_Out, node: L_Node): string {
  if (out === L_Out.True) {
    return `<True Expression> ${node}`;
  } else if (out === L_Out.Unknown) {
    return `[Unknown Expression] ${node}`;
  } else if (out === L_Out.Error) {
    return `[Error Expression] ${node}`;
  } else if (out === L_Out.False) {
    return `[False Expression] ${node}`;
  }

  return `???`;
}

export function lstLengthNotEql(
  env: L_Env,
  lst1: unknown[],
  lst2: unknown[]
): L_Out {
  env.newMessage(
    `Error: ${lst1} and ${lst2} are supposed to have the same length.`
  );

  return L_Out.Error;
}

export function reportNotAllFactsInGivenFactAreDeclared(
  env: L_Env,
  fact: ToCheckNode
): L_Out {
  env.newMessage(`Error! Not all of facts in ${fact} are declared`);
  return L_Out.Error;
}

export function reportNewVars(env: L_Env, vars: string[]): L_Out {
  env.newMessage(`[new var] ${vars}`);
  return L_Out.True;
}

export function reportNewExist(env: L_Env, exist: OptNode): L_Out {
  env.newMessage(`[new exist] ${exist}`);
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

export function reportFailedFunctionName(
  env: L_Env,
  funcName: string
): boolean {
  env.newMessage(`<${funcName}> Failed`);
  return false;
}

export function L_ReportErr(env: L_Env, func: Function, node?: L_Node): L_Out {
  env.newMessage(`<${func.name}> Failed`);
  if (node !== undefined) env.newMessage(`Failed: ${node}`);
  return L_Out.Error;
}
