import { DefNode, KnowNode, LiTeXNode, LiTexNodeType } from "./ast";
import { LiTeXEnv } from "./env";

export function nodeExec(env: LiTeXEnv, node: LiTeXNode) {
  switch (node.type) {
    case LiTexNodeType.DefNode:
      defExec(env, node as DefNode);
    case LiTexNodeType.KnowNode:
      knowExec(env, node as KnowNode);
  }
}

export function defExec(env: LiTeXEnv, node: DefNode) {
  env.defs.set(node.declOptName, node);
}

export function knowExec(env: LiTeXEnv, node: KnowNode) {
  for (let i = 0; i < node.facts.length; i++) {
    const curNode = node.facts[i];
    switch (curNode.type) {
      case LiTexNodeType.DefNode:
    }
  }
}
