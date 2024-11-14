import { OptNode } from "./ast.ts";
import { L_Env } from "./L_Env.ts";
import { RType } from "./L_Executor.ts";

// deno-lint-ignore ban-types
export const L_Builtins = new Map<string, Function>();

L_Builtins.set("is_property", (env: L_Env, node: OptNode): RType => {
  const out = env.getDeclaredFact(node.vars[0]);
  if (out === undefined) {
    env.newMessage(`is_property error: ${node.name} undeclared.`);
    return RType.Error;
  } else {
    if (node.vars.length !== Number(node.vars[1])) {
      env.newMessage(
        `is_property error: ${node.name} requires ${
          out.vars.length
        } parameters, ${Number(node.vars[1])} given.`
      );
    } else {
      return RType.True;
    }
  }
});
