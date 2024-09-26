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
  CanBeKnownNode,
  makeCallOptNode,
  // OnlyIfFactNode,
} from "./ast";
import { FactAboutGivenOpt, LiTeXEnv } from "./env";
import { builtInCallOptNames } from "./executor_builtins";
import { IndexOfGivenSymbolInCallOpt } from "./common";

export enum ResultType {
  True,
  KnowTrue,
  DefTrue,
  False,
  Unknown,
  Error,
}

function getErrorInfo(s: string = ""): ResultInfoType {
  return { type: ResultType.Error, message: s };
}

function getTrueInfo(s: string = ""): ResultInfoType {
  return { type: ResultType.True, message: s };
}

function getKnowTrueInfo(s: string = ""): ResultInfoType {
  return { type: ResultType.KnowTrue, message: s };
}

function getDefTrueInfo(s: string = ""): ResultInfoType {
  return { type: ResultType.DefTrue, message: s };
}

function getFalseInfo(s: string = ""): ResultInfoType {
  return { type: ResultType.False, message: s };
}

function getUnknownInfo(s: string = ""): ResultInfoType {
  return { type: ResultType.Unknown, message: s };
}

export type ResultInfoType = { type: ResultType; message: string };

export function catchRuntimeError(env: LiTeXEnv, err: any, m: string) {
  if (err instanceof Error) {
    if (err.message) handleRuntimeError(env, err.message);
  }
  handleRuntimeError(env, m);
}

export function handleRuntimeError(env: LiTeXEnv, message: string) {
  env.pushErrorMessage("Runtime error: " + message);
}

export function nodeExec(env: LiTeXEnv, node: LiTeXNode): ResultInfoType {
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

  return getErrorInfo("");
}

function callOptsExec(env: LiTeXEnv, node: CallOptsNode): ResultInfoType {
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
      return getUnknownInfo();
    }

    // switch (env.optType(node.nodes[i].optName)) {
    //   case LiTexNodeType.DefNode:
    //     knowDefCallOptExec(env, node.nodes[i]);
    //     break;
    // case LiTexNodeType.InferNode:
    //   knowInferCallOptExec(env, node.nodes[i]);
    //   break;
    // }
  }

  return getTrueInfo();
}

function inferExec(
  env: LiTeXEnv,
  node: InferNode,
  fatherName: string = ""
): ResultInfoType {
  try {
    if (env.keyInDefs(node.declOptName)) {
      throw Error(node.declOptName + " has already been declared.");
    } else if (env.infers.has(node.declOptName)) {
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

    return getTrueInfo();
  } catch (error) {
    catchRuntimeError(env, error, "infer");
    return getUnknownInfo();
  }
}

function knowExec(env: LiTeXEnv, node: KnowNode | LetNode): ResultInfoType {
  let facts: CanBeKnownNode[] = [];
  if (node.type === LiTexNodeType.KnowNode) {
    facts = (node as KnowNode).facts;
  } else if (node.type === LiTexNodeType.LetNode) {
    facts = (node as LetNode).properties;
  }

  for (let i = 0; i < facts.length; i++) {
    const curNode: CanBeKnownNode = facts[i];
    let result: ResultInfoType;
    switch (curNode.type) {
      case LiTexNodeType.CallOptNode:
        result = knowCallOptExec(env, curNode as CallOptNode);
        if (result.type !== ResultType.True) return result;
        break;
      // When knowing def and infer, we not only emit them into env.defs/infers, we also store facts
      case LiTexNodeType.DefNode:
        result = knowDefExec(env, curNode as DefNode);
        if (result.type !== ResultType.KnowTrue) return result;
        break;
      case LiTexNodeType.InferNode:
        result = knowInferExec(env, curNode as InferNode);
        if (result.type !== ResultType.KnowTrue) return result;
        break;
      // case LiTexNodeType.OnlyIfFactNode:
      //   result = knowOnlyIfFactExec(env, curNode as OnlyIfFactNode);
      //   if (result !== ResultType.True) return result;
      //   break;
      default:
        return getErrorInfo("");
    }
  }
  return getTrueInfo();
}

// function knowOnlyIfFactExec(env: LiTeXEnv, node: OnlyIfFactNode): ResultInfoType{
//   return getTrueInfo();
// }
function knowDefExec(env: LiTeXEnv, node: DefNode): ResultInfoType {
  defExec(env, node);
  knowCallOptExec(
    env,
    makeCallOptNode(node.declOptName, node.params, node.declOptName.split("::"))
  );
  return getKnowTrueInfo();
}

function knowInferExec(env: LiTeXEnv, node: InferNode): ResultInfoType {
  inferExec(env, node);
  knowCallOptExec(
    env,
    makeCallOptNode(node.declOptName, node.params, node.declOptName.split("::"))
  );
  return getKnowTrueInfo();
}

function knowCallOptExec(env: LiTeXEnv, node: CallOptNode): ResultInfoType {
  switch (env.optType(node.optName)) {
    case LiTexNodeType.InferNode:
      const result = knowInferCallOptExec(env, node);
      if (result === ResultType.Unknown) return getUnknownInfo();
      break;
    case LiTexNodeType.DefNode:
      knowDefCallOptExec(env, node);
      break;
  }
  env.newFact(node);
  return getKnowTrueInfo();
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
    return getErrorInfo("");
  }
}

function letExec(env: LiTeXEnv, node: LetNode): ResultInfoType {
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
    return getErrorInfo("");
  }
}

function defExec(env: LiTeXEnv, node: DefNode): ResultInfoType {
  try {
    env.defs.set(node.declOptName, node);

    return getDefTrueInfo();
  } catch (error) {
    catchRuntimeError(env, error, "def");
    return getErrorInfo("");
  }
}

function knowDefCallOptExec(env: LiTeXEnv, node: CallOptNode): ResultInfoType {
  const defNode = env.defs.get(node.optName) as DefNode;

  const freeToFixedMap: Map<string, string> = getFreeToFixedMap(defNode, node);
  defNode.emitOnlyIfs(env, freeToFixedMap);
  return getTrueInfo();
}
