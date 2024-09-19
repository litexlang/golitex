import { DefNode, KnowNode, LiTeXNode, LiTexNodeType } from "./ast";
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
      defExec(env, node as DefNode);
    case LiTexNodeType.KnowNode:
      knowExec(env, node as KnowNode);
  }
}

export function defExec(env: LiTeXEnv, node: DefNode) {
  try {
    if (env.keyInDefs(node.declOptName)) {
      throw Error(node.declOptName + " has already been declared.");
    }
    env.defs.set(node.declOptName, node);
  } catch (error) {
    catchRuntimeError(env, error, "def");
  }
}

export function knowExec(env: LiTeXEnv, node: KnowNode) {
  for (let i = 0; i < node.facts.length; i++) {
    const curNode = node.facts[i];
    switch (curNode.type) {
      case LiTexNodeType.DefNode:
        defExec(env, curNode as DefNode);
      case LiTexNodeType.ExistNode:
    }
  }
}
