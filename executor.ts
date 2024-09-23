import {
  CallOptNode,
  CallOptsNode,
  InferNode,
  ExistNode,
  IffNode,
  IfNode,
  IndexOfGivenSymbol,
  KnowNode,
  LiTeXNode,
  LiTexNodeType,
  OnlyIfNode,
} from "./ast";
import { LiTeXEnv } from "./env";
import { builtInCallOptNames } from "./executor_builtins";

export enum ResultType {
  True,
  False,
  Unknown,
  Error,
}

export function catchRuntimeError(env: LiTeXEnv, err: any, m: string) {
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
    case LiTexNodeType.InferNode:
      return inferExec(env, node as InferNode);
    case LiTexNodeType.KnowNode:
      return knowExec(env, node as KnowNode);
    case LiTexNodeType.CallOptsNode:
      return callOptsExec(env, node as CallOptsNode);
  }

  return ResultType.Error;
}

function callOptsExec(env: LiTeXEnv, node: CallOptsNode): ResultType {
  for (let i = 0; i < node.nodes.length; i++) {
    const nodeName: string = node.nodes[i].optName;
    if (nodeName in builtInCallOptNames) {
      const result = builtInCallOptNames[nodeName](env, node.nodes[i]);
      if (result !== ResultType.True) {
        return result;
      } else {
        continue;
      }
    }

    if (!env.isCallOptFact(node.nodes[i])) {
      return ResultType.Unknown;
    } else {
      callOptExec(env, node.nodes[i]);
    }
  }

  return ResultType.True;
}

function inferExec(
  env: LiTeXEnv,
  node: InferNode,
  fatherName: string = ""
): ResultType {
  try {
    if (env.keyInDefs(node.declOptName)) {
      throw Error(node.declOptName + " has already been declared.");
    }
    let sonNamePrefix: string = "";
    if (fatherName === "") {
      sonNamePrefix = node.declOptName + "::";
      env.infers.set(node.declOptName, node);
    } else {
      sonNamePrefix = fatherName + node.declOptName + "::";
      env.infers.set(fatherName + node.declOptName, node);
    }

    for (const item of node.requirements) {
      if (item.type === LiTexNodeType.InferNode) {
        inferExec(env, item as InferNode, sonNamePrefix);
      } else if (item.type === LiTexNodeType.KnowNode) {
        for (const subitem of (item as KnowNode).facts) {
          if (subitem.type === LiTexNodeType.InferNode) {
            inferExec(env, subitem as InferNode, sonNamePrefix);
          }
        }
      }
    }

    for (const item of node.onlyIfExprs) {
      if (item.type === LiTexNodeType.InferNode) {
        inferExec(env, item as InferNode, sonNamePrefix);
      } else if (item.type === LiTexNodeType.KnowNode) {
        for (const subitem of (item as KnowNode).facts) {
          if (subitem.type === LiTexNodeType.InferNode) {
            inferExec(env, subitem as InferNode, sonNamePrefix);
          }
        }
      }
    }

    return ResultType.True;
  } catch (error) {
    catchRuntimeError(env, error, "infer");
    return ResultType.Unknown;
  }
}

function addNewOnlyIfsToDefs(
  env: LiTeXEnv,
  leftDef: InferNode,
  left: CallOptNode,
  right: CallOptNode
): ResultType {
  try {
    let params: string[][] = [];
    for (let i = 0; i < right.paramsLst().length; i++) {
      params.push([]);
    }

    let optNames: string[] = right.paramsLst();
    for (let i = 0; i < right.paramsLst().length; i++) {
      for (let j = 0; j < right.paramsLst()[i].length; j++) {
        const index = IndexOfGivenSymbol(left, right.paramsLst()[i][j]);
        if (!index) params[i][j] = right.paramsLst()[i][j];
        else {
          params[i].push(leftDef.params[index[0]][index[1]]);
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

function knowIfExec(env: LiTeXEnv, node: IfNode): ResultType {
  //? Unfinished: might introduce repeated facts
  try {
    const key: string = node.right.optName;
    if (!env.keyInDefs(key)) return ResultType.Unknown;
    const InferNode = env.infers.get(key);

    for (const item of node.left as CallOptsNode[]) {
      for (const subitem of item.nodes as CallOptNode[])
        addNewOnlyIfsToDefs(
          env,
          InferNode as InferNode,
          node.right,
          subitem as CallOptNode
        );
    }

    return ResultType.True;
  } catch (error) {
    catchRuntimeError(env, error, "if");
    return ResultType.Error;
  }
}

function knowOnlyIfExec(env: LiTeXEnv, node: OnlyIfNode): ResultType {
  //? Unfinished: might introduce repeated facts
  try {
    const key: string = node.left.optName;
    if (!env.keyInDefs(key)) return ResultType.Unknown;
    const InferNode = env.infers.get(key);

    for (const item of node.right as CallOptsNode[]) {
      for (const subitem of item.nodes as CallOptNode[])
        addNewOnlyIfsToDefs(
          env,
          InferNode as InferNode,
          node.left,
          subitem as CallOptNode
        );
    }

    return ResultType.True;
  } catch (error) {
    catchRuntimeError(env, error, "if");
    return ResultType.Error;
  }
}

function knowIffExec(env: LiTeXEnv, node: IffNode): ResultType {
  //? Unfinished: might introduce repeated facts
  try {
    const leftKey: string = node.left.optName;
    if (!env.keyInDefs(leftKey)) return ResultType.Unknown;
    const leftDefNode = env.infers.get(leftKey);

    const rightKey: string = node.right.optName;
    if (!env.keyInDefs(rightKey)) return ResultType.Unknown;
    const rightDefNode = env.infers.get(rightKey);

    addNewOnlyIfsToDefs(env, leftDefNode as InferNode, node.left, node.right);
    addNewOnlyIfsToDefs(env, rightDefNode as InferNode, node.right, node.left);

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
      case LiTexNodeType.InferNode:
        inferExec(env, curNode as InferNode);
        break;
      case LiTexNodeType.ExistNode:
        existExec(env, curNode as ExistNode);
        break;
      case LiTexNodeType.CallOptNode:
        knowCallOptExec(env, curNode as CallOptNode);
        break;
      case LiTexNodeType.OnlyIfNode:
        knowOnlyIfNodeExec(env, curNode as OnlyIfNode);
        break;
      case LiTexNodeType.IffNode:
        knowIffExec(env, curNode as IffNode);
        break;
      case LiTexNodeType.IfNode:
        knowIfExec(env, curNode as IfNode);
        break;
      case LiTexNodeType.OnlyIfNode:
        knowOnlyIfExec(env, curNode as OnlyIfNode);
        break;
    }
  }
  return ResultType.True;
}

function existExec(env: LiTeXEnv, node: ExistNode) {}

function knowCallOptExec(env: LiTeXEnv, node: CallOptNode) {
  env.newFact(node);
  callOptExec(env, node);
}

function knowOnlyIfNodeExec(env: LiTeXEnv, node: OnlyIfNode) {
  // const node = env.defs.get(node.left.)
}

function callOptExec(env: LiTeXEnv, node: CallOptNode) {
  const optName: string = node.optName;
  const InferNode: InferNode | undefined = env.infers.get(optName);
  if (InferNode === undefined) {
    return;
  }

  const fixedVars: string[][] = node.optParams;
  const freeVars: string[][] = InferNode.params;

  for (const item of InferNode.onlyIfExprs) {
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

  for (const [index, opt] of node.getOptNameParamsPairs().entries()) {
    const newOpt: [string, string[]] = [node.getParaNames()[index], []];

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

    fixedNode.pushNewNameParamsPair(newOpt);
  }

  return fixedNode;
}
