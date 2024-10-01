import {
  CallOptNode,
  CallOptsNode,
  KnowNode,
  LiTeXNode,
  LiTexNodeType,
  LetNode,
  FactNode,
  CanBeKnownNode,
  TemplateNode,
  // HaveNode,
} from "./ast";
import { LiTeXBuiltinKeywords } from "./builtins";
import { LiTeXEnv } from "./env";

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
  HaveError,
  HaveTrue,
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
  [ResultType.HaveError]: "have: error",
  [ResultType.HaveTrue]: "have: true",
};

export function execInfo(t: ResultType, s: string = ""): ExecInfo {
  return { type: t, message: s };
}

export type ExecInfo = { type: ResultType; message: string };

export function catchRuntimeError(env: LiTeXEnv, err: any, m: string): string {
  if (err instanceof Error) {
    if (err.message) handleRuntimeError(env, err.message);
  }
  return handleRuntimeError(env, m);
}

export function handleRuntimeError(env: LiTeXEnv, message: string): string {
  return "Runtime error: " + message;
}

export function nodeExec(env: LiTeXEnv, node: LiTeXNode): ExecInfo {
  switch (node.type) {
    case LiTexNodeType.DefNode:
    case LiTexNodeType.InferNode:
    case LiTexNodeType.ExistNode:
      return templateDeclExec(env, node as TemplateNode);
    case LiTexNodeType.KnowNode:
      return knowExec(env, node as KnowNode);
    case LiTexNodeType.CallOptsNode:
      //TODO : Emit facts
      return callOptsExec(env, node as CallOptsNode);
    // case LiTexNodeType.HaveNode:
    //   return haveExec(env, node as HaveNode);
  }

  return execInfo(ResultType.Error, "Invalid Expression.");
}

function callOptsExec(env: LiTeXEnv, node: CallOptsNode): ExecInfo {
  for (const fact of (node as CallOptsNode).nodes) {
    let res = callOptExec(env, fact as CallOptNode);
    if (res.type !== ResultType.True) return res;
  }
  return execInfo(ResultType.True);
}

function callOptExec(env: LiTeXEnv, node: CallOptNode): ExecInfo {
  try {
    const builtinFunc = LiTeXBuiltinKeywords[node.optName];
    if (builtinFunc) {
      return builtinFunc(env, node);
    }

    const relatedTemplate = env.getDeclaredTemplate(node);
    if (!relatedTemplate)
      return execInfo(ResultType.False, node.optName + " is not declared.");

    const res = relatedTemplate.checkByFixingFreeVars(
      env,
      node,
      relatedTemplate.requirements
    );
    if (res.type === ResultType.KnowTrue) {
      relatedTemplate.emitCallOptByFixingFreeVars(
        env,
        node,
        relatedTemplate.onlyIfExprs
      );
      return execInfo(
        ResultType.KnowTrue,
        `${node.optName} itself and all of its requirements are true`
      );
    }

    // for (let i = 0; i < relatedTemplate.facts.length; i++) {
    //   if (
    //     checkParams(relatedTemplate.facts[i].params, node.optParams) &&
    //     relatedTemplate.facts[i].activated
    //   ) {
    //     switch (relatedTemplate.type) {
    //       case LiTexNodeType.ExistNode: {
    //         relatedTemplate.emitCallOptByFixingFreeVars(
    //           env,
    //           node,
    //           relatedTemplate.requirements
    //         );
    //       }
    //       case LiTexNodeType.DefNode: {
    //       }
    //     }
    //     return execInfo(ResultType.True);
    //   }
    // }

    return execInfo(
      ResultType.DefTrue,
      `${node.optName} itself is true while its requirements are not all satisfied.`
    );
  } catch (error) {
    catchRuntimeError(env, error, "check");
    return execInfo(ResultType.Error);
  }
}

export function checkParams(arr1: string[][], arr2: string[][]): boolean {
  if (arr1.length !== arr2.length) {
    return false;
  }

  for (let i = 0; i < arr1.length; i++) {
    if (arr1[i].length !== arr2[i].length) {
      return false;
    }

    for (let j = 0; j < arr1[i].length; j++) {
      // If arr1[i][j] starts with '#', consider it a match regardless of arr2[i][j]
      if (!arr1[i][j].startsWith("#") && arr1[i][j] !== arr2[i][j]) {
        return false;
      }
    }
  }

  return true;
}

function templateDeclExec(env: LiTeXEnv, node: TemplateNode): ExecInfo {
  try {
    (env.declaredTemplates as Map<string, TemplateNode>).set(
      node.declOptName,
      node
    );
    // move templates(pure, questionMark) from node.onlyIfs to node.declaredTemplates
    node.initDeclaredTemplates();

    return execInfo(ResultType.DefTrue);
  } catch (error) {
    catchRuntimeError(env, error, "template declaration");
    return execInfo(ResultType.DefError);
  }
}

function knowExec(env: LiTeXEnv, node: KnowNode | LetNode): ExecInfo {
  try {
    let facts: CanBeKnownNode[] = [];
    let isKnowEverything: Boolean = false;
    if (node.type === LiTexNodeType.KnowNode) {
      facts = (node as KnowNode).facts;
      isKnowEverything = (node as KnowNode).isKnowEverything;
    } else if (node.type === LiTexNodeType.LetNode) {
      facts = (node as LetNode).properties;
    }

    let res: ExecInfo = { type: ResultType.Error, message: "" };
    for (const fact of facts) {
      switch (fact.type) {
        case LiTexNodeType.CallOptNode: {
          if (isKnowEverything)
            res = knowEverythingCallOptExec(env, fact as CallOptNode);
          else res = knowCallOptExec(env, fact as CallOptNode);
          break;
        }
        case LiTexNodeType.DefNode:
        case LiTexNodeType.InferNode: {
          res = templateDeclExec(env, fact as TemplateNode);
          if (isKnowEverything) {
            res = knowEverythingCallOptExec(
              env,
              CallOptNode.create((fact as TemplateNode).declOptName, [
                (fact as TemplateNode).freeVars,
              ])
            );
          } else {
            res = knowCallOptExec(
              env,
              CallOptNode.create((fact as TemplateNode).declOptName, [
                (fact as TemplateNode).freeVars,
              ])
            );
          }
          break;
        }
      }
      if (res.type !== ResultType.KnowTrue) return res;
    }

    return execInfo(ResultType.KnowTrue);
  } catch (error) {
    catchRuntimeError(env, error, "know");
    return execInfo(ResultType.KnowError);
  }
}

export function knowEverythingCallOptExec(
  env: LiTeXEnv,
  fact: CallOptNode
): ExecInfo {
  let res: ExecInfo = { type: ResultType.Error, message: "" };
  res = knowCallOptExec(env, fact);

  const template = env.getDeclaredTemplate(fact as CallOptNode);
  if (!template)
    throw Error(`${(fact as CallOptNode).optName} has not been declared.`);

  template?.emitCallOptByFixingFreeVars(
    env,
    fact,
    template.onlyIfExprs,
    template.requirements
  );

  return execInfo(ResultType.KnowTrue);
}

export function knowCallOptExec(env: LiTeXEnv, node: CallOptNode): ExecInfo {
  let relatedTemplate = env.getDeclaredTemplate(node.optName);

  if (!relatedTemplate)
    return execInfo(
      ResultType.KnowUndeclared,
      node.optName + " has not declared"
    );

  let res = (
    env.getDeclaredTemplate(node.optNameAsLst[0]) as TemplateNode
  ).knowCallOptExecCheck(node);
  if (res.type !== ResultType.KnowTrue) return res;

  env.pushCallOptFact(node);

  return execInfo(ResultType.KnowTrue);
}

// export function haveExec(env: LiTeXEnv, node: HaveNode): ExecInfo {
//   try {
//     const relatedOpt = node.opt;
//     const existTemplate = env.getDeclaredTemplate(relatedOpt);

//     if (existTemplate?.type !== LiTexNodeType.ExistNode) {
//       throw new Error(`${relatedOpt.optName} is not a exist opt.`);
//     }

//     existTemplate.emitCallOptByFixingFreeVars(
//       env,
//       relatedOpt,
//       existTemplate.requirements
//     );

//     return execInfo(ResultType.HaveTrue);
//   } catch (error) {
//     if (error instanceof Error) {
//       return execInfo(ResultType.HaveError, error.message);
//     } else {
//       return execInfo(ResultType.HaveError, String(error));
//     }
//   }
// }
