import {
  CallOptNode,
  CallOptsNode,
  InferNode,
  KnowNode,
  LiTeXNode,
  LiTexNodeType,
  LetNode,
  DefNode,
  getFreeToFixedMap,
  FactNode,
  CanBeKnownNode,
  TemplateNode,
} from "./ast";
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
    case LiTexNodeType.InferNode:
      return templateDeclExec(env, node as TemplateNode);
    case LiTexNodeType.KnowNode:
      return knowExec(env, node as KnowNode);
    case LiTexNodeType.CallOptsNode:
      //TODO : Emit facts
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
      if (checkParams(value, node.optParams)) {
        return resultInfo(ResultType.True);
      }
    }

    return resultInfo(ResultType.Unknown);
  } catch (error) {
    catchRuntimeError(env, error, "check");
    return resultInfo(ResultType.Error);
  }

  function checkParams(arr1: string[][], arr2: string[][]): boolean {
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
}

function knowFactExec(env: LiTeXEnv, node: FactNode): ExecInfo {
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
