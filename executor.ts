import {
  CallOptNode,
  CallOptsNode,
  DefNode,
  ExistNode,
  KnowNode,
  LiTeXNode,
  LiTexNodeType,
} from "./ast";
import { LiTeXEnv } from "./env";

function catchRuntimeError(env: LiTeXEnv, err: any, m: string) {
  if (err instanceof Error) {
    if (err.message) handleRuntimeError(env, err.message);
  }
  handleRuntimeError(env, m);
}

export function handleRuntimeError(env: LiTeXEnv, message: string) {
  env.pushErrorMessage("Runtime error: " + message);
}

export function nodeExec(env: LiTeXEnv, node: LiTeXNode) {
  switch (node.type) {
    case LiTexNodeType.DefNode:
      return defExec(env, node as DefNode);
    case LiTexNodeType.KnowNode:
      return knowExec(env, node as KnowNode);
    case LiTexNodeType.CallOptsNode:
      return callOptsExec(env, node as CallOptsNode);
  }
}

function callOptsExec(env: LiTeXEnv, node: CallOptsNode) {
  for (let i = 0; i < node.nodes.length; i++) {
    if (!env.isFact(node.nodes[i])) return false;
  }

  return true;
}

function defExec(env: LiTeXEnv, node: DefNode) {
  try {
    if (env.keyInDefs(node.declOptName)) {
      throw Error(node.declOptName + " has already been declared.");
    }
    env.defs.set(node.declOptName, node);
  } catch (error) {
    catchRuntimeError(env, error, "def");
  }
}

function knowExec(env: LiTeXEnv, node: KnowNode) {
  for (let i = 0; i < node.facts.length; i++) {
    const curNode = node.facts[i];
    switch (curNode.type) {
      case LiTexNodeType.DefNode:
        defExec(env, curNode as DefNode);
      case LiTexNodeType.ExistNode:
        existExec(env, curNode as ExistNode);
      case LiTexNodeType.CallOptNode:
        knowCallOptParse(env, curNode as CallOptNode);
    }
  }
}

function existExec(env: LiTeXEnv, node: ExistNode) {}

function knowCallOptParse(env: LiTeXEnv, node: CallOptNode) {
  env.newFact(node);
}
