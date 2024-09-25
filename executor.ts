import {
  CallOptNode,
  CallOptsNode,
  InferNode,
  ExistNode,
  // IffNode,
  // IfNode,
  KnowNode,
  LiTeXNode,
  LiTexNodeType,
  // OnlyIfNode,
  LetNode,
  // CanBeKnownNode,
  DefNode,
  getFreeToFixedMap,
  FactNode,
  OnlyIfFactNode,
} from "./ast";
import { FactAboutGivenOpt, LiTeXEnv } from "./env";
import { builtInCallOptNames } from "./executor_builtins";
import { IndexOfGivenSymbolInCallOpt } from "./common";

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
    case LiTexNodeType.LetNode:
      return letExec(env, node as LetNode);
    case LiTexNodeType.DefNode:
      return defExec(env, node as DefNode);
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
    }

    switch (env.optType(node.nodes[i].optName)) {
      case LiTexNodeType.DefNode:
        knowDefCallOptExec(env, node.nodes[i]);
        break;
      case LiTexNodeType.InferNode:
        knowInferCallOptExec(env, node.nodes[i]);
        break;
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
      }
    }

    for (const item of node.onlyIfExprs) {
      if (item.type === LiTexNodeType.InferNode) {
        inferExec(env, item as InferNode, sonNamePrefix);
      }
    }

    return ResultType.True;
  } catch (error) {
    catchRuntimeError(env, error, "infer");
    return ResultType.Unknown;
  }
}

function knowExec(env: LiTeXEnv, node: KnowNode | LetNode): ResultType {
  let facts: FactNode[] = [];
  if (node.type === LiTexNodeType.KnowNode) {
    facts = (node as KnowNode).facts;
  } else if (node.type === LiTexNodeType.LetNode) {
    facts = (node as LetNode).properties;
  }

  for (let i = 0; i < facts.length; i++) {
    const curNode: FactNode = facts[i];
    let result: ResultType = ResultType.Unknown;
    switch (curNode.type) {
      case LiTexNodeType.CallOptNode:
        result = knowCallOptExec(env, curNode as CallOptNode);
        if (result !== ResultType.True) return result;
        break;
      case LiTexNodeType.OnlyIfFactNode:
        result = knowOnlyIfFactExec(env, curNode as OnlyIfFactNode);
        if (result !== ResultType.True) return result;
        break;
    }
  }
  return ResultType.True;
}

function knowOnlyIfFactExec(env: LiTeXEnv, node: OnlyIfFactNode): ResultType {
  return ResultType.True;
}

function knowCallOptExec(env: LiTeXEnv, node: CallOptNode): ResultType {
  switch (env.optType(node.optName)) {
    case LiTexNodeType.InferNode:
      const result = knowInferCallOptExec(env, node);
      if (result === ResultType.Unknown) return ResultType.Unknown;
      break;
    case LiTexNodeType.DefNode:
      knowDefCallOptExec(env, node);
      break;
  }
  env.newFact(node);
  return ResultType.True;
}

function knowInferCallOptExec(env: LiTeXEnv, node: CallOptNode) {
  try {
    const relatedInferNode = env.infers.get(node.optName) as InferNode;
    const freeToFixedMap: Map<string, string> = getFreeToFixedMap(
      relatedInferNode,
      node
    );

    const checkResult: ResultType = relatedInferNode.checkRequirements(
      env,
      freeToFixedMap
    );
    if (!(checkResult === ResultType.True)) {
      return checkResult;
    }

    relatedInferNode.emitOnlyIfs(env, freeToFixedMap);
  } catch (error) {
    catchRuntimeError(env, error, "know infer");
    return ResultType.Error;
  }
}

function letExec(env: LiTeXEnv, node: LetNode): ResultType {
  try {
    for (const item of node.params) {
      if (env.declaredVars.includes(item)) {
        throw Error(item + "has already been declared");
      }
    }

    env.declaredVars = [...env.declaredVars, ...node.params];

    return knowExec(env, node);
  } catch (error) {
    catchRuntimeError(env, error, "let");
    return ResultType.Error;
  }
}

function defExec(env: LiTeXEnv, node: DefNode): ResultType {
  try {
    env.defs.set(node.declOptName, node);
    return ResultType.True;
  } catch (error) {
    catchRuntimeError(env, error, "def");
    return ResultType.Error;
  }
}

function knowDefCallOptExec(env: LiTeXEnv, node: CallOptNode): ResultType {
  const defNode = env.defs.get(node.optName) as DefNode;

  const freeToFixedMap: Map<string, string> = getFreeToFixedMap(defNode, node);
  defNode.emitOnlyIfs(env, freeToFixedMap);
  return ResultType.True;
}
