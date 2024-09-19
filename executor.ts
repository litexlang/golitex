import {
  CallOptNode,
  CallOptsNode,
  DefNode,
  ExistNode,
  KnowNode,
  LiTeXNode,
  LiTexNodeType,
  OnlyIfNode,
} from "./ast";
import { LiTeXEnv } from "./env";

enum ResultType {
  True,
  False,
  Unknown,
  Error,
}

function catchRuntimeError(env: LiTeXEnv, err: any, m: string) {
  if (err instanceof Error) {
    if (err.message) handleRuntimeError(env, err.message);
  }
  handleRuntimeError(env, m);
}

export function handleRuntimeError(env: LiTeXEnv, message: string) {
  env.pushErrorMessage("Runtime error: " + message);
}

export function nodeExec(env: LiTeXEnv, node: LiTeXNode): ResultType {
  switch (node.type) {
    case LiTexNodeType.DefNode:
      return defExec(env, node as DefNode);
    case LiTexNodeType.KnowNode:
      return knowExec(env, node as KnowNode);
    case LiTexNodeType.CallOptsNode:
      return callOptsExec(env, node as CallOptsNode);
  }

  return ResultType.Error;
}

function callOptsExec(env: LiTeXEnv, node: CallOptsNode): ResultType {
  for (let i = 0; i < node.nodes.length; i++) {
    if (!env.isFact(node.nodes[i])) return ResultType.Unknown;
  }

  return ResultType.True;
}

function defExec(
  env: LiTeXEnv,
  node: DefNode,
  fatherName: string = ""
): ResultType {
  try {
    if (env.keyInDefs(node.declOptName)) {
      throw Error(node.declOptName + " has already been declared.");
    }
    let sonNamePrefix: string = "";
    if (fatherName === "") {
      sonNamePrefix = node.declOptName + "::";
      env.defs.set(node.declOptName, node);
    } else {
      sonNamePrefix = fatherName + node.declOptName + "::";
      env.defs.set(fatherName + node.declOptName, node);
    }

    for (const item of node.onlyIfExprs) {
      if (item.type === LiTexNodeType.DefNode) {
        defExec(env, item as DefNode, sonNamePrefix);
      } else if (item.type === LiTexNodeType.KnowNode) {
        for (const subitem of (item as KnowNode).facts) {
          if (subitem.type === LiTexNodeType.DefNode) {
            defExec(env, subitem as DefNode, sonNamePrefix);
          }
        }
      }
    }

    return ResultType.True;
  } catch (error) {
    catchRuntimeError(env, error, "def");
    return ResultType.Unknown;
  }
}

// The interesting part: Even if you don't declare opt, you can still know facts about that opt. That means we don't need to claim what "set" or "number" means, and directly 'know set(a)' when necessary
function knowExec(env: LiTeXEnv, node: KnowNode): ResultType {
  for (let i = 0; i < node.facts.length; i++) {
    const curNode = node.facts[i];
    switch (curNode.type) {
      case LiTexNodeType.DefNode:
        defExec(env, curNode as DefNode);
      case LiTexNodeType.ExistNode:
        existExec(env, curNode as ExistNode);
      case LiTexNodeType.CallOptNode:
        knowCallOptParse(env, curNode as CallOptNode);
      case LiTexNodeType.OnlyIfNode:
        knowOnlyIfNodeParse(env, curNode as OnlyIfNode);
    }
  }
  return ResultType.True;
}

function existExec(env: LiTeXEnv, node: ExistNode) {}

function knowCallOptParse(env: LiTeXEnv, node: CallOptNode) {
  env.newFact(node);
}

function knowOnlyIfNodeParse(env: LiTeXEnv, node: OnlyIfNode) {
  // const node = env.defs.get(node.left.)
}
