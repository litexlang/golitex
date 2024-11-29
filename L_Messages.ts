import type { L_Env } from "./L_Env.ts";
import { L_Out } from "./L_Executor.ts";
import type { L_Node, OptNode, ToCheckNode } from "./L_Nodes.ts";

export function lstLengthNotEql(
  env: L_Env,
  lst1: unknown[],
  lst2: unknown[],
): L_Out {
  env.newMessage(
    `Error: ${lst1} and ${lst2} are supposed to have the same length.`,
  );

  return L_Out.Error;
}

export function reportNotAllFactsInGivenFactAreDeclared(
  env: L_Env,
  fact: ToCheckNode,
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
