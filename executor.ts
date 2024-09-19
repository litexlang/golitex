import { DefNode, LiTeXNode } from "./ast";
import { LiTeXEnv } from "./env";

export function nodeExec(env: LiTeXEnv, node: LiTeXNode) {}

export function defExec(env: LiTeXEnv, node: DefNode) {
  env.defs.set(node.declOptName, node);
}
