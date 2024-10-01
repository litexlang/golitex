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
  makeTemplateNodeFact,
  DefNode,
} from "./ast";
import { LiTeXBuiltinKeywords } from "./builtins";
import { LiTeXEnv } from "./env";

export enum ResultType {
  True, // not only used as True for callOptExec, but also as a generic type passed between subFunctions.
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
  LetTrue,
  LetError,
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
  [ResultType.LetError]: "let: error",
  [ResultType.LetTrue]: "let: true",
};

export function execInfo(t: ResultType, s: string = ""): ExecInfo {
  return { type: t, message: s };
}

export type ExecInfo = { type: ResultType; message: string };

function checkFixedOpt(env: LiTeXEnv, callOpt: CallOptNode): ExecInfo {
  const relatedTemplate = env.getDeclaredTemplate(callOpt);
  if (!relatedTemplate)
    return execInfo(ResultType.Error, callOpt.optName + " is not declared.");
  for (let i = 0; i < relatedTemplate.facts.length; i++) {
    const res = _checkParamsUsingTwoArrayArrays(
      relatedTemplate.facts[i].params,
      callOpt.optParams
    );
    if (res) return execInfo(ResultType.True);
  }
  return execInfo(ResultType.Unknown);
}

function infoTypeIsNotTrue(info: ExecInfo) {
  if (info.type !== ResultType.True) return true;
  else return false;
}

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
      return callOptsExec(env, node as CallOptsNode);
    case LiTexNodeType.LetNode:
      return letExec(env, node as LetNode);
  }

  return execInfo(ResultType.Error, "Invalid Expression.");
}

function letExec(env: LiTeXEnv, node: LetNode): ExecInfo {
  // Check ofr duplicate variable declarations
  const duplicateVars = node.vars.filter((v) => env.declaredVars.includes(v));
  if (duplicateVars.length > 0) {
    return execInfo(
      ResultType.LetError,
      `Error: Variable(s) ${duplicateVars.join(", ")} already declared in this scope.`
    );
  }

  env.declaredVars = env.declaredVars.concat(node.vars) as string[];
  for (let i = 0; i < node.properties.length; i++) {
    knowCallOptExec(env, node.properties[i]);
  }

  return execInfo(ResultType.LetTrue);
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

    // check itself
    let res: ExecInfo = checkFixedOpt(env, node);
    if (infoTypeIsNotTrue(res))
      return execInfo(res.type, `${node.optName} itself is not satisfied.`);

    // check all requirements
    res = fixFreeVarsAndCallHandlerFunc(
      env,
      node,
      _checkOpt,
      relatedTemplate.requirements
    );

    if (infoTypeIsNotTrue(res))
      return execInfo(
        res.type,
        `${node.optName} itself is true while its requirements are not satisfied.`
      );

    // emit
    fixFreeVarsAndCallHandlerFunc(
      env,
      node,
      _pushNewOpt,
      relatedTemplate.onlyIfExprs
    );

    return execInfo(
      ResultType.DefTrue,
      `${node.optName} itself and its requirements are all satisfied.`
    );
  } catch (error) {
    catchRuntimeError(env, error, "check");
    return execInfo(ResultType.Error);
  }
}

export function _checkParamsUsingTwoArrayArrays(
  arr1: string[][],
  arr2: string[][]
): boolean {
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

  fixFreeVarsAndCallHandlerFunc(
    env,
    fact,
    _pushNewOpt,
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

  fixFreeVarsAndCallHandlerFunc(env, node, _pushNewOpt, [node]);

  return execInfo(ResultType.KnowTrue);
}

function fixFreeVarsAndCallHandlerFunc(
  env: LiTeXEnv,
  fixedNode: CallOptNode, // the fullCallOpt, including params of father opts. 'this' is in the lowest opt of the CallOpt.
  doWhenFreeVarsAreFixed: (
    env: LiTeXEnv,
    fixedParams: string[][],
    relatedTemplate: TemplateNode
  ) => ExecInfo,
  emitWhat: LiTeXNode[], // pass in template.requirement or template.onlyIfExprs
  additionalEmit?: LiTeXNode[]
): ExecInfo {
  //! Chain reaction is not allowed, maybe I should add some syntax to allow user to use chain reaction.
  const freeToFixed = new Map<string, string>();

  for (
    let optIndex = 0,
      curTemplate = env.getDeclaredTemplate(fixedNode.optNameAsLst[0]);
    optIndex < fixedNode.optParams.length;
    optIndex++,
      curTemplate = curTemplate.declaredTemplates.get(
        fixedNode.optNameAsLst[optIndex]
      )
  ) {
    const argumentsOfCurrentOpt: string[] = fixedNode.optParams[optIndex];

    if (!curTemplate) return execInfo(ResultType.Error);

    for (
      let argIndex = 0;
      argIndex < argumentsOfCurrentOpt.length;
      argIndex++
    ) {
      if (argIndex < curTemplate.freeVars.length) {
        freeToFixed.set(
          curTemplate.freeVars[argIndex] as string,
          argumentsOfCurrentOpt[argIndex]
        );
      }
    }
  }

  for (let i = 0; i < emitWhat.length; i++) {
    if (emitWhat[i] instanceof CallOptsNode) {
      for (const onlyIfFact of (emitWhat[i] as CallOptsNode).nodes) {
        const result: ExecInfo = doToCallOptAfterFixingVars(onlyIfFact);
        if (result.type !== ResultType.True) return result;
      }
    } else if (emitWhat[i] instanceof CallOptNode) {
      const result: ExecInfo = doToCallOptAfterFixingVars(
        emitWhat[i] as CallOptNode
      );
      if (result.type !== ResultType.True) return result;
    }
  }

  if (additionalEmit) {
    for (let i = 0; i < additionalEmit.length; i++) {
      if (additionalEmit[i] instanceof CallOptsNode) {
        for (const onlyIfFact of (additionalEmit[i] as CallOptsNode).nodes) {
          const result: ExecInfo = doToCallOptAfterFixingVars(onlyIfFact);
          if (result.type !== ResultType.True) return result;
        }
      } else if (additionalEmit[i] instanceof CallOptNode) {
        const result: ExecInfo = doToCallOptAfterFixingVars(
          additionalEmit[i] as CallOptNode
        );
        if (result.type !== ResultType.True) return result;
      }
    }
  }

  //TODO: Has not emitted onlyIfs that binds to specific fact instead of Template.onlyIfs.
  return execInfo(ResultType.True);

  function doToCallOptAfterFixingVars(callOpt: CallOptNode): ExecInfo {
    const res: {
      newParams: string[][];
      relatedTemplate: TemplateNode | undefined;
    } = getFixedParamsAndRelatedTemplate(callOpt);
    if (!res.relatedTemplate) return execInfo(ResultType.Error);
    return doWhenFreeVarsAreFixed(env, res.newParams, res.relatedTemplate);
  }

  function getFixedParamsAndRelatedTemplate(factToBeEmitted: CallOptNode): {
    newParams: string[][];
    relatedTemplate: TemplateNode | undefined;
  } {
    // replace freeVars with fixedVars
    const newParams: string[][] = [];
    for (let j = 0; j < factToBeEmitted.optParams.length; j++) {
      const subParams: string[] = [];
      for (let k = 0; k < factToBeEmitted.optParams[j].length; k++) {
        const fixed = freeToFixed.get(factToBeEmitted.optParams[j][k]);
        if (fixed) subParams.push(fixed);
        else subParams.push(factToBeEmitted.optParams[j][k]);
      }
      newParams.push(subParams);
    }

    const relatedTemplate = env.getDeclaredTemplate(factToBeEmitted);
    return { newParams: newParams, relatedTemplate: relatedTemplate };
  }
}

const _pushNewOpt = (
  env: LiTeXEnv,
  newParams: string[][],
  relatedTemplate: TemplateNode
) => {
  relatedTemplate.newFact(env, makeTemplateNodeFact(newParams));
  return execInfo(ResultType.True);
};

const _checkOpt = (
  env: LiTeXEnv,
  newParams: string[][],
  relatedTemplate: TemplateNode
) => {
  for (let i = 0; i < relatedTemplate?.facts.length; i++) {
    const res = _checkParamsUsingTwoArrayArrays(
      relatedTemplate.facts[i].params,
      newParams //
    );
    if (!res) return execInfo(ResultType.Unknown);
  }
  return execInfo(ResultType.True);
};

export function _paramsInOptAreDeclared(
  env: LiTeXEnv,
  optParams: string[][] | string[]
): boolean {
  if (optParams.length === 0) return true;

  // Check if optParams is a 2D array
  const is2DArray = Array.isArray(optParams[0]);

  if (is2DArray) {
    // Handle 2D array case
    for (let i = 0; i < optParams.length; i++) {
      for (let j = 0; j < (optParams[i] as string[]).length; j++) {
        if (!env.declaredVars.includes((optParams[i] as string[])[j]))
          return false;
      }
    }
  } else {
    // Handle 1D array case
    for (let i = 0; i < optParams.length; i++) {
      if (!env.declaredVars.includes(optParams[i] as string)) return false;
    }
  }

  return true;
}
