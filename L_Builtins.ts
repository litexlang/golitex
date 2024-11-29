import { L_Node, OptNode, ToCheckNode } from "./L_Nodes";
import { L_Env } from "./L_Env";
import { L_Out, nodeExec } from "./L_Executor";
import { checkOptLiterally } from "./L_Checker";
import { reportNewExist } from "./L_Messages";
import { KnownExist } from "./L_Memory";

// deno-lint-ignore ban-types
export const L_Builtins = new Map<string, Function>();

export function isToCheckBuiltin(node: ToCheckNode) {
  return (node instanceof OptNode) && (L_Builtins.get(node.name) !== undefined);
}

// node looks like is_property(OptName)
L_Builtins.set("is_property", (env: L_Env, node: OptNode): L_Out => {
  try {
    const out = env.getDef(node.vars[0]);
    if (out === undefined) {
      env.newMessage(
        `is_property error: ${node.name} is an undeclared operator.`,
      );
      return L_Out.Error;
    } else {
      if (out.vars.length !== Number(node.vars[1])) {
        env.newMessage(
          `is_property error: ${node.name} requires ${out.vars.length} parameters, ${
            Number(node.vars[1])
          } given.`,
        );
        return L_Out.Error;
      } else {
        return L_Out.True;
      }
    }
  } catch {
    return L_Out.Error;
  }
});

// node looks like exist(OptName, v1,v2...vn)
L_Builtins.set("exist", (env: L_Env, node: OptNode): L_Out => {
  try {
    if (env.isExisted(node.vars[0]) === node.isT) {
      return L_Out.True;
    }

    const toCheck = new OptNode(node.vars[0], node.vars.slice(1));

    // Why checkOptLiterally? because I want to make exist as "user-is-responsible-for-checking" as possible
    const out = checkOptLiterally(env, toCheck);
    if (out === L_Out.True) {
      env.newExist(node.vars[0], new KnownExist(node.isT));
    }

    return out;
  } catch {
    return L_Out.Error;
  }
});

export function proveExist(
  env: L_Env,
  toProve: OptNode,
  block: L_Node[],
): L_Out {
  try {
    const newEnv = new L_Env(env);
    for (const node of block) {
      const out = nodeExec(newEnv, node, true);
      if (out !== L_Out.True) return out;
    }

    // deno-lint-ignore ban-types
    const checker = L_Builtins.get("exist") as Function;
    const out = checker(newEnv, toProve);
    if (out !== L_Out.True) return out;

    env.newExist(toProve.name, new KnownExist(toProve.isT));
    return reportNewExist(env, toProve);
  } catch {
    return env.errMesReturnL_Out(toProve);
  }
}
