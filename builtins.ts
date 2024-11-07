import { L_Node } from "./ast.ts";
import { L_Env } from "./L_Env.ts";
import { RType } from "./L_Executor.ts";

export const L_Builtins = new Map<
  string,
  (env: L_Env, node: L_Node) => RType
>();

// L_Builtins.set("isProp", (env: L_Env, node: L_Node): RType => {
//   return node instanceof OptNode && env.getDeclFact(node.fullName)
//     ? RType.True
//     : RType.Error;
// });
