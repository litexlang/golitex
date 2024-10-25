import { FactNode, L_Node, OptNode } from "./ast";
import { L_Env } from "./env";
import { RType } from "./executor";

export const L_Builtins = new Map<
  string,
  (env: L_Env, node: L_Node) => RType
>();

L_Builtins.set("isProp", (env: L_Env, node: L_Node): RType => {
  return node instanceof OptNode && env.getDeclFact(node.fullName)
    ? RType.True
    : RType.Error;
});
