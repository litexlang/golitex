import { OptNode } from "./L_Nodes.ts";
import { L_Env } from "./L_Env.ts";
import { L_Out } from "./L_Executor.ts";
import { checkOptLiterally } from "./L_Checker.ts";

// deno-lint-ignore ban-types
export const L_Builtins = new Map<string, Function>();

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
    if (env.isExisted(node.vars[0])) {
      return L_Out.True;
    }

    const toCheck = new OptNode(node.vars[0], node.vars.slice(1));

    // Why checkOptLiterally? because I want to make exist as "user-is-responsible-for-checking" as possible
    const out = checkOptLiterally(env, toCheck);
    if (out === L_Out.True) {
      env.newExist(node.vars[0]);
    }

    return out;
  } catch {
    return L_Out.Error;
  }
});
