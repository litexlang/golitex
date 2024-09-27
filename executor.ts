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
  TemplateNode,
  // OnlyIfFactNode,
} from "./ast";
import { FactAboutGivenOpt, LiTeXEnv } from "./env";
import { builtInCallOptNames } from "./executor_builtins";
import { IndexOfGivenSymbolInCallOpt, OptsConnectionSymbol } from "./common";

export enum ResultType {
  True,
  KnowTrue,
  KnowError,
  KnowUndeclared,
  DefTrue,
  DefError,
  False,
  Unknown,
  Error,
}

export const resultTypeMap: { [key in ResultType]: string } = {
  [ResultType.Error]: "error",
  [ResultType.False]: "check: false",
  [ResultType.True]: "check: true",
  [ResultType.Unknown]: "check: unknown",
  [ResultType.KnowTrue]: "know: true",
  [ResultType.DefTrue]: "def: true",
  [ResultType.KnowError]: "know: error",
  [ResultType.DefError]: "def: error",
  [ResultType.KnowUndeclared]: "know: undeclared opt",
};

export function resultInfo(t: ResultType, s: string = ""): ExecInfo {
  return { type: t, message: s };
}

export type ExecInfo = { type: ResultType; message: string };

export function catchRuntimeError(env: LiTeXEnv, err: any, m: string) {
  if (err instanceof Error) {
    if (err.message) handleRuntimeError(env, err.message);
  }
  handleRuntimeError(env, m);
}

export function handleRuntimeError(env: LiTeXEnv, message: string) {
  env.pushErrorMessage("Runtime error: " + message);
}

export function nodeExec(env: LiTeXEnv, node: LiTeXNode): ExecInfo {
  switch (node.type) {
    case LiTexNodeType.DefNode:
    // return defExec(env, node as DefNode);
    case LiTexNodeType.InferNode:
      // return inferExec(env, node as InferNode);
      return templateDeclExec(env, node as TemplateNode);
    case LiTexNodeType.KnowNode:
      return knowExec(env, node as KnowNode);
    case LiTexNodeType.CallOptsNode:
      for (const fact of (node as CallOptsNode).nodes) {
        let res = checkFactExec(env, fact as CallOptNode);
        if (res.type !== ResultType.True) return res;
      }
      return resultInfo(ResultType.True);
    case LiTexNodeType.LetNode:
      return letExec(env, node as LetNode);
  }

  return resultInfo(ResultType.Error, "Invalid Expression.");
}

function checkFactExec(env: LiTeXEnv, node: CallOptNode): ExecInfo {
  try {
    const relatedTemplate = env.getDeclaredTemplate(node);
    if (!relatedTemplate)
      return resultInfo(ResultType.False, node.optName + " is not declared.");
    for (const value of relatedTemplate?.facts) {
      if (areNestedArraysEqual(value, node.optParams)) {
        return resultInfo(ResultType.True);
      }
    }

    return resultInfo(ResultType.Unknown);
  } catch (error) {
    catchRuntimeError(env, error, "check");
    return resultInfo(ResultType.Error);
  }

  function areNestedArraysEqual(arr1: string[][], arr2: string[][]): boolean {
    if (arr1.length !== arr2.length) {
      return false;
    }

    for (let i = 0; i < arr1.length; i++) {
      if (arr1[i].length !== arr2[i].length) {
        return false;
      }

      for (let j = 0; j < arr1[i].length; j++) {
        if (arr1[i][j] !== arr2[i][j]) {
          return false;
        }
      }
    }

    return true;
  }
}

function templateDeclExec(env: LiTeXEnv, node: TemplateNode): ExecInfo {
  try {
    env.declaredTemplates.set(node.declOptName, node);
    node.initDeclaredTemplates();

    return resultInfo(ResultType.DefTrue);
  } catch (error) {
    catchRuntimeError(env, error, "template declaration");
    return resultInfo(ResultType.DefError);
  }
}

function callOptsExec(env: LiTeXEnv, node: CallOptsNode): ExecInfo {
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

    const res = env.checkFact(node.nodes[i]);
    if (res.type !== ResultType.True) return res;

    // if (!env.isCallOptFact(node.nodes[i])) {
    //   return resultInfo(ResultType.Unknown);
    // }

    // switch (env.optType(node.nodes[i].optName)) {
    //   case LiTexNodeType.DefNode:
    //     knowDefCallOptExec(env, node.nodes[i]);
    //     break;
    // case LiTexNodeType.InferNode:
    //   knowInferCallOptExec(env, node.nodes[i]);
    //   break;
    // }
  }

  return resultInfo(ResultType.True);
}

// function inferExec(
//   env: LiTeXEnv,
//   node: InferNode,
//   fatherName: string = ""
// ): ExecInfo {
//   try {
//     if (env.keyInDefs(node.declOptName)) {
//       throw Error(node.declOptName + " has already been declared.");
//     } else if (env.infers.has(node.declOptName)) {
//       throw Error(node.declOptName + " has already been declared.");
//     }

//     let sonNamePrefix: string = "";
//     if (fatherName === "") {
//       sonNamePrefix = node.declOptName + ":";
//       env.infers.set(node.declOptName, node);
//     } else {
//       sonNamePrefix = fatherName + node.declOptName + ":";
//       env.infers.set(fatherName + node.declOptName, node);
//     }

//     return resultInfo(ResultType.True);
//   } catch (error) {
//     catchRuntimeError(env, error, "infer");
//     return resultInfo(ResultType.Unknown);
//   }
// }

function knowExec(env: LiTeXEnv, node: KnowNode | LetNode): ExecInfo {
  //TODO: Needs to check whether a template is declared
  let facts: CanBeKnownNode[] = [];
  if (node.type === LiTexNodeType.KnowNode) {
    facts = (node as KnowNode).facts;
  } else if (node.type === LiTexNodeType.LetNode) {
    facts = (node as LetNode).properties;
  }

  let res: ExecInfo = { type: ResultType.Error, message: "" };
  for (const fact of facts) {
    switch (fact.type) {
      case LiTexNodeType.CallOptNode:
        res = env.pushNewFact(fact as FactNode);
    }
    if (res.type !== ResultType.KnowTrue) return res;
  }

  return resultInfo(ResultType.KnowTrue);

  // for (let i = 0; i < facts.length; i++) {
  //   const curNode: CanBeKnownNode = facts[i];
  //   let result: ExecInfo;
  //   switch (curNode.type) {
  //     case LiTexNodeType.CallOptNode:
  //       // result = knowCallOptExec(env, curNode as CallOptNode);
  //       result = knowFactExec(env, curNode as CallOptNode);
  //       if (result.type !== ResultType.KnowTrue) return result;
  //       break;
  // When knowing def and infer, we not only emit them into env.defs/infers, we also store facts
  // case LiTexNodeType.DefNode:
  //   result = knowDefExec(env, curNode as DefNode);
  //   if (result.type !== ResultType.KnowTrue) return result;
  //   break;
  // case LiTexNodeType.InferNode:
  //   result = knowInferExec(env, curNode as InferNode);
  //   if (result.type !== ResultType.KnowTrue) return result;
  //   break;
  // case LiTexNodeType.OnlyIfFactNode:
  //   result = knowOnlyIfFactExec(env, curNode as OnlyIfFactNode);
  //   if (result !== ResultType.True) return result;
  //   break;
  //     default:
  //       return resultInfo(ResultType.Error, "");
  //   }
  // }
  // return resultInfo(ResultType.KnowTrue);
}

function knowFactExec(env: LiTeXEnv, node: FactNode): ExecInfo {
  // function knowDefCallOptExec(env: LiTeXEnv, node: CallOptNode): ExecInfo {
  //   const defNode = env.defs.get(node.optName) as DefNode;

  //   const freeToFixedMap: Map<string, string> = getFreeToFixedMap(
  //     defNode,
  //     node
  //   );
  //   defNode.emitOnlyIfs(env, freeToFixedMap);
  //   return resultInfo(ResultType.True);
  // }

  // function knowInferCallOptExec(env: LiTeXEnv, node: CallOptNode) {
  //   try {
  //     const relatedInferNode = env.infers.get(node.optName) as InferNode;
  //     const freeToFixedMap: Map<string, string> = getFreeToFixedMap(
  //       relatedInferNode,
  //       node
  //     );

  //     const checkResult: ResultType = relatedInferNode.checkRequirements(
  //       env,
  //       freeToFixedMap
  //     );
  //     if (!(checkResult === ResultType.True)) {
  //       return checkResult;
  //     }

  //     relatedInferNode.emitOnlyIfs(env, freeToFixedMap);
  //   } catch (error) {
  //     catchRuntimeError(env, error, "know infer");
  //     return resultInfo(ResultType.Error, "");
  //   }
  // }

  /**Check whether the called fact is declared. */
  let relatedTemplate: TemplateNode | undefined = env.getDeclaredTemplate(
    node.optName
  );

  if (!relatedTemplate)
    return resultInfo(
      ResultType.KnowUndeclared,
      node.optName + " has not declared"
    );

  /**Check fact and emit onlyIfs. */
  switch (env.optType(node.optName)) {
    case LiTexNodeType.InferNode:
      {
        // const relatedInferNode = env.getDeclaredTemplate(
        //   node.optName
        // ) as InferNode;
        const inferFreeToFixedMap: Map<string, string> = getFreeToFixedMap(
          relatedTemplate as InferNode,
          node
        );

        const checkResult: ResultType = (
          relatedTemplate as InferNode
        ).checkRequirements(env, inferFreeToFixedMap);
        if (!(checkResult === ResultType.True)) {
          return resultInfo(checkResult);
        }

        (relatedTemplate as InferNode).emitOnlyIfs(env, inferFreeToFixedMap);
      }
      break;

    case LiTexNodeType.DefNode:
      {
        const defNode = env.getDeclaredTemplate(node.optName) as DefNode;

        const freeToFixedMap: Map<string, string> = getFreeToFixedMap(
          defNode,
          node
        );
        defNode.emitOnlyIfs(env, freeToFixedMap);
      }
      break;
  }

  env.newFact(node);
  return resultInfo(ResultType.KnowTrue);
}

// function knowOnlyIfFactExec(env: LiTeXEnv, node: OnlyIfFactNode): ExecInfo{
//   return resultInfo(ResultType.True);
// }
// function knowDefExec(env: LiTeXEnv, node: DefNode): ExecInfo {
//   defExec(env, node);
//   knowCallOptExec(
//     env,
//     makeCallOptNode(node.declOptName, node.params, node.declOptName.split(":"))
//   );
//   return resultInfo(ResultType.KnowTrue);
// }

// function knowInferExec(env: LiTeXEnv, node: InferNode): ExecInfo {
//   inferExec(env, node);
//   knowCallOptExec(
//     env,
//     makeCallOptNode(node.declOptName, node.params, node.declOptName.split(":"))
//   );
//   return resultInfo(ResultType.KnowTrue);
// }

function letExec(env: LiTeXEnv, node: LetNode): ExecInfo {
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
    return resultInfo(ResultType.Error, "");
  }
}

// function defExec(
//   env: LiTeXEnv,
//   node: DefNode,
//   fatherName: string = ""
// ): ExecInfo {
//   try {
//     env.defs.set(fatherName + node.declOptName, node);

//     // for (const value of node.onlyIfExprs) {
//     //   switch (value.type) {
//     //     case LiTexNodeType.DefNode:
//     //     case LiTexNodeType.InferNode:
//     //       node.declaredTemplates.set(node.declOptName, value as TemplateNode);
//     //       break;
//     //   }
//     // }

//     return resultInfo(ResultType.DefTrue);
//   } catch (error) {
//     catchRuntimeError(env, error, "def");
//     return resultInfo(ResultType.Error, "");
//   }
// }

// function emitNewFacts(template: TemplateNode, fact: FactNode): ExecInfo {

// }
