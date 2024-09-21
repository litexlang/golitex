import {
  CallOptNode,
  CallOptsNode,
  DefNode,
  ExistNode,
  IffNode,
  IndexOfGivenSymbol,
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
    if (!env.isCallOptFact(node.nodes[i])) {
      return ResultType.Unknown;
    } else {
      emitCallOptDescendants(env, node.nodes[i]);
    }
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

    for (const item of node.requirements) {
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

function addNewOnlyIfsToDefs(
  env: LiTeXEnv,
  leftDef: DefNode,
  left: CallOptNode,
  right: CallOptNode
): ResultType {
  try {
    let params: string[][] = [];
    let optNames: string[] = right.opts.map((e) => e[0]);
    for (let i = 0; i < right.paramsLst().length; i++) {
      for (let j = 0; j < right.paramsLst()[i].length; j++) {
        const index = IndexOfGivenSymbol(left, right.paramsLst()[i][j]);
        if (!index) params[i][j] = right.paramsLst()[i][j];
        else {
          params[i][j] = leftDef.params[i][j];
        }
      }
    }
    let optParamsLst: [string, string[]][] = optNames.map((e, index) => [
      e,
      params[index],
    ]);
    leftDef.onlyIfExprs.push(new CallOptsNode([new CallOptNode(optParamsLst)]));

    return ResultType.True;
  } catch (error) {
    catchRuntimeError(env, error, "onlyIf/Iff/If");
    return ResultType.Error;
  }
}

function knowIffExec(env: LiTeXEnv, node: IffNode): ResultType {
  try {
    const leftKey: string = node.left.opts.map((e) => e[0]).join("::");
    if (!env.keyInDefs(leftKey)) return ResultType.Unknown;
    const leftDefNode = env.defs.get(leftKey);

    const rightKey: string = node.right.opts.map((e) => e[0]).join("::");
    if (!env.keyInDefs(rightKey)) return ResultType.Unknown;
    const rightDefNode = env.defs.get(rightKey);

    addNewOnlyIfsToDefs(env, leftDefNode as DefNode, node.left, node.right);
    addNewOnlyIfsToDefs(env, rightDefNode as DefNode, node.right, node.left);

    return ResultType.True;
  } catch (error) {
    catchRuntimeError(env, error, "iff");
    return ResultType.Error;
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
        knowCallOptExec(env, curNode as CallOptNode);
      case LiTexNodeType.OnlyIfNode:
        knowOnlyIfNodeExec(env, curNode as OnlyIfNode);
      case LiTexNodeType.IfNode:
        knowIffExec(env, curNode as IffNode);
    }
  }
  return ResultType.True;
}

function existExec(env: LiTeXEnv, node: ExistNode) {}

function knowCallOptExec(env: LiTeXEnv, node: CallOptNode) {
  env.newFact(node);
  emitCallOptDescendants(env, node);
}

function knowOnlyIfNodeExec(env: LiTeXEnv, node: OnlyIfNode) {
  // const node = env.defs.get(node.left.)
}

function emitCallOptDescendants(env: LiTeXEnv, node: CallOptNode) {
  const optName: string = node.opts.map((e) => e[0]).join("::");
  const defNode: DefNode | undefined = env.defs.get(optName);
  if (defNode === undefined) {
    return;
  }

  const fixedVars: string[][] = node.opts.map((e) => e[1]);
  const freeVars: string[][] = defNode.params;

  for (const item of defNode.onlyIfExprs) {
    if (item.type === LiTexNodeType.CallOptsNode) {
      //! If I put knowCallOptExec here, chain reaction will happen, and there will be more and more new facts generated.
      for (const callOpt of (item as CallOptsNode).nodes) {
        // const callOpt = replaceFreeVarInCallOptOfDefNode(freeCallOpt);

        const fixedNode = freeVarsToFixedVars(callOpt, fixedVars, freeVars);

        env.newFact(fixedNode as CallOptNode);
      }
    }
  }
}

function freeVarsToFixedVars(
  node: CallOptNode,
  fixedVars: string[][],
  freeVars: string[][]
) {
  const fixedNode = new CallOptNode([]);

  for (const [index, opt] of (node.opts as [string, string[]][]).entries()) {
    const newOpt: [string, string[]] = [node.opts[index][0], []];

    for (const variable of opt[1] as string[]) {
      let hasDefined = false;
      for (let i = freeVars.length - 1; i >= 0; i--) {
        for (let j = 0; j < freeVars[i].length; j++) {
          if (variable === freeVars[i][j]) {
            hasDefined = true;
            break;
          }
        }
        if (hasDefined) break;
      }
      if (!hasDefined) newOpt[1].push(variable);
    }

    fixedNode.opts.push(newOpt);
  }

  return fixedNode;
}
