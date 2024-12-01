import { L_Node, OptNode, ToCheckNode } from "./L_Nodes";
import { L_Env } from "./L_Env";
import { L_Out, nodeExec } from "./L_Executor";
import { checkOptLiterally } from "./L_Checker";
import { reportNewExist } from "./L_Messages";
import { KnownExist } from "./L_Memory";

export const L_BuiltinsKeywords: string[] = ["is_property", "exist", "or"];

// Define an interface for built-in function types
export interface BuiltinFunction {
  (env: L_Env, node: OptNode): L_Out;
}

export function isToCheckBuiltin(node: ToCheckNode): boolean {
  return node instanceof OptNode && L_Builtins.get(node.name) !== undefined;
}

// Create a map of built-in function names to their implementations
export const L_Builtins = new Map<string, BuiltinFunction>([
  ["is_property", isPropertyBuiltin],
  ["exist", existBuiltin],
]);

// Separate functions from the map
export function isPropertyBuiltin(env: L_Env, node: OptNode): L_Out {
  try {
    const out = env.getDef(node.vars[0]);
    if (out === undefined) {
      env.newMessage(
        `is_property error: ${node.name} is an undeclared operator.`
      );
      return L_Out.Error;
    } else {
      if (out.vars.length !== Number(node.vars[1])) {
        env.newMessage(
          `is_property error: ${node.name} requires ${
            out.vars.length
          } parameters, ${Number(node.vars[1])} given.`
        );
        return L_Out.Error;
      } else {
        return L_Out.True;
      }
    }
  } catch {
    return L_Out.Error;
  }
}

export function existBuiltin(env: L_Env, node: OptNode): L_Out {
  try {
    for (let i = 0; i < node.vars.length; i++) {
      if (env.isExisted(node.vars[i]) === node.isT) {
        return L_Out.True;
      }

      const toCheck = new OptNode(
        node.vars[i],
        (node.checkVars as string[][])[i]
      );

      // Strict checking for existence
      const out = checkOptLiterally(env, toCheck);
      if (out === L_Out.True) {
        env.newExist(node.vars[i], new KnownExist(node.isT));
      } else {
        return out;
      }
    }

    return L_Out.True;
  } catch {
    return L_Out.Error;
  }
}
