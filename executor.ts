import {
  CallOptNode,
  CallOptsNode,
  KnowNode,
  LiTeXNode,
  LiTexNodeType,
  LetNode,
  CanBeKnownNode,
  TemplateNode,
  TemplateNodeFact,
  ProveNode,
  YAProveNode,
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
  ProveError,
  ProveTrue,
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
  [ResultType.ProveError]: "prove: error",
  [ResultType.ProveTrue]: "prove: true",
};

export function execInfoIsTrue(res: ExecInfo) {
  return [
    ResultType.True,
    ResultType.KnowError,
    ResultType.DefTrue,
    ResultType.HaveError,
    ResultType.LetError,
    ResultType.ProveError,
  ].includes(res.type);
}

export const execInfo = (t: ResultType, s: string = "") => {
  return { type: t, message: s };
};
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
      return yaKnowExec(env, node as KnowNode);
    case LiTexNodeType.CallOptsNode:
      return callOptsExec(env, node as CallOptsNode);
    case LiTexNodeType.LetNode:
      return letExec(env, node as LetNode);
    case LiTexNodeType.ProofNode:
      return yaProveExec(env, node as YAProveNode);
  }

  return execInfo(ResultType.Error, "Invalid Expression.");
}

//TODO: add requirements
function proveNode(env: LiTeXEnv, node: ProveNode): ExecInfo {
  const relatedTemplate = env.getDeclaredTemplate(node.templateName);
  if (!relatedTemplate)
    return execInfo(
      ResultType.ProveError,
      `${node.templateName} is not declared.`
    );
  env = new LiTeXEnv(env);

  for (let i = 0; i < node.freeVars.length; i++) {
    if (node.freeVars[i].startsWith("*")) continue;
    if (node.freeVars[i].startsWith("#"))
      return execInfo(
        ResultType.ProveError,
        "parameters in requirement should not start with #"
      );
    else {
      let res = env.newVar(node.freeVars[i]);
      if (!res)
        return execInfo(
          ResultType.ProveError,
          "two parameters have the same name."
        );
    }
  }

  // emit the requirements in prove

  //! several if-thens: 1. callOpt vs callOpts 2. with * or with no *.
  for (let i = 0; i < relatedTemplate.requirements.length; i++) {
    const requirement = relatedTemplate.requirements[i];
    if (requirement instanceof CallOptNode) {
      //! I notice that the current prove has wrong structure because it cannot prove xxx:yyy, the reason why we use [relatedTemplate.freeVars] here is that one day it will become relatedTemplate.fullFreeVars (after fullFreeVars are introduced into proveNode)
      const result = _findReqVarIndexInTemplate(
        requirement.optParams as string[][],
        relatedTemplate.freeVars
      );

      // fixedParamForRequirement
      let fixed: string[][] = [];
      for (let i = 0; i < requirement.optParams.length; i++) {
        fixed.push([]);
        for (let j = 0; j < requirement.optParams[i].length; j++) {
          fixed[i].push("");
        }
      }

      for (let item of result) {
        fixed[item.requirementIndex[0]][item.requirementIndex[1]] =
          node.freeVars[item.templateParamsIndex];
      }

      if (!_allStartWithAsterisk(fixed))
        env.newSymbolsFactsPair(
          fixed.map(
            (e) => e.map((el) => (el.startsWith("*") ? el.slice(1) : el)) // no need to always use * as prefix
          ),
          env.getDeclaredTemplate(requirement) as TemplateNode
        );
      else {
        fixed = fixed.map(
          (e) => e.map((el) => (el.startsWith("*") ? el.slice(1) : el)) // no need to always use * as prefix
        );
        if (
          !env.symbolsFactsPairIsTrue(
            fixed,
            env.getDeclaredTemplate(requirement) as TemplateNode
          )
        ) {
          return execInfo(
            ResultType.ProveError,
            `requirements of ${fixed} are not satisfied.`
          );
        }
      }
    }
  }

  //! Currently requirement cannot see what is defined in block
  for (let fact of node.requirements) {
    // all parameters of current fact start with *
    let allStartWithStar = true;
    for (let i = 0; i < (fact as CallOptNode).optParams.length; i++) {
      for (let j = 0; j < (fact as CallOptNode).optParams[i].length; j++) {
        if (!(fact as CallOptNode).optParams[i][j].startsWith("*"))
          allStartWithStar = false;
      }
    }

    const relatedTemplate = env.getDeclaredTemplate(fact as CallOptNode);

    if (relatedTemplate) {
      if (!allStartWithStar) {
        // emit the requirements in opt
        env.newSymbolsFactsPair(
          (fact as CallOptNode).optParams.map(
            (e) => e.map((el) => (el.startsWith("*") ? el.slice(1) : el)) // no need to always use * as prefix
          ),
          relatedTemplate
        );
      } else {
        let res = env.symbolsFactsPairIsTrue(
          (fact as CallOptNode).optParams.map((e) =>
            e.map((el) => el.slice(1))
          ),
          relatedTemplate
        );
        if (!res)
          return execInfo(
            ResultType.Error,
            `${res} does not have fact ${relatedTemplate.declOptName}`
          );
      }
    } else {
      return execInfo(
        ResultType.Error,
        (fact as CallOptNode).optName + " is not defined."
      );
    }
  }

  let res: ExecInfo = execInfo(ResultType.ProveTrue);

  let onlyIfsThatNeedsCheck = [...relatedTemplate.onlyIfExprs];

  for (let onlyIfCallOpts of node.onlyIfExprs) {
    if (onlyIfCallOpts instanceof CallOptsNode) {
      for (let onlyIf of (onlyIfCallOpts as CallOptsNode).nodes) {
        processOnlyIfCallOpt(onlyIf);
      }
    } else {
      processOnlyIfCallOpt(onlyIfCallOpts as CallOptNode);
    }
  }

  if (onlyIfsThatNeedsCheck.length === 0) return execInfo(ResultType.ProveTrue);
  else
    return execInfo(
      ResultType.ProveError,
      "not all onlyIfs in template are satisfied."
    );

  function processOnlyIfCallOpt(onlyIf: CallOptNode) {
    res = nodeExec(env, onlyIf);
    if (onlyIf instanceof CallOptNode) {
      for (let i = 0; i < onlyIfsThatNeedsCheck.length; i++) {
        let onlyIfThatNeedsCheck = onlyIfsThatNeedsCheck[i];
        let isTrue = fixFreeVarsAndCallHandlerFunc(env, onlyIf, _checkOpt, [
          onlyIfThatNeedsCheck,
        ]);
        if (execInfoIsTrue(isTrue)) {
          fixFreeVarsAndCallHandlerFunc(env, onlyIf, _pushNewOpt, [
            onlyIfThatNeedsCheck,
          ]);
          onlyIfsThatNeedsCheck.splice(i, 1);
          i--;
        }
      }
    }
  }

  function _findReqVarIndexInTemplate(
    requirementVars: string[][],
    relatedSingleTemplateFreeVars: string[]
  ): {
    requirementIndex: [number, number];
    templateParamsIndex: number;
  }[] {
    const mapping: {
      requirementIndex: [number, number];
      templateParamsIndex: number;
    }[] = [];
    for (let i = 0; i < requirementVars.length; i++) {
      for (let j = 0; j < requirementVars[i].length; j++) {
        for (let k = 0; k < relatedSingleTemplateFreeVars.length; k++) {
          if (relatedSingleTemplateFreeVars[k] === requirementVars[i][j]) {
            mapping.push({ requirementIndex: [i, j], templateParamsIndex: k });
            break;
          }
        }
      }
    }

    return mapping;
  }
}

function letExec(env: LiTeXEnv, node: LetNode): ExecInfo {
  // Check ofr duplicate variable declarations
  const notDeclared = node.vars.filter((v) => env.declaredVars.includes(v));
  if (!notDeclared) {
    return execInfo(
      ResultType.LetError,
      `Error: Variable(s) ${node.vars.join(", ")} already declared in this scope.`
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
    if (!execInfoIsTrue(res)) return res;
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
    let isTrue: Boolean = env.symbolsFactsPairIsTrue(
      node.optParams,
      relatedTemplate
    );

    if (!isTrue)
      return execInfo(
        ResultType.Unknown,
        `${node.optName} itself is not satisfied.`
      );

    // check all requirements
    const mapping = relatedTemplate.fix(node);
    if (!mapping) return execInfo(ResultType.Error);
    isTrue = relatedTemplate.requirementsSatisfied(env, mapping);
    if (!isTrue)
      return execInfo(
        ResultType.Unknown,
        `${node.optName} itself is true while its requirements are not satisfied.`
      );

    // let res = fixFreeVarsAndCallHandlerFunc(
    //   env,
    //   node,
    //   _checkOpt,
    //   relatedTemplate.requirements
    // );

    // if (_isNotResultTypeTrue(res))
    //   return execInfo(
    //     res.type,
    //     `${node.optName} itself is true while its requirements are not satisfied.`
    //   );

    // emit
    relatedTemplate.emitOnlyIfs(env, mapping);

    // fixFreeVarsAndCallHandlerFunc(
    //   env,
    //   node,
    //   _pushNewOpt,
    //   relatedTemplate.onlyIfExprs.filter((v) => {
    //     if (v instanceof CallOptNode) return true;
    //     else return false;
    //   })
    // );

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
    // Here we overwrite the original declared functions.
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

export function knowEverythingCallOptExec(
  env: LiTeXEnv,
  fact: CallOptNode
): ExecInfo {
  let res: ExecInfo = { type: ResultType.Error, message: "" };
  res = knowCallOptExec(env, fact);

  const template = env.getDeclaredTemplate(fact as CallOptNode);
  if (!template)
    throw Error(`${(fact as CallOptNode).optName} has not been declared.`);

  res = fixFreeVarsAndCallHandlerFunc(
    env,
    fact,
    _pushNewOpt,
    template.onlyIfExprs,
    template.requirements
  );

  if (_isNotResultTypeTrue(res)) return res;

  return execInfo(ResultType.KnowTrue);
}

export function knowCallOptExec(env: LiTeXEnv, node: CallOptNode): ExecInfo {
  let relatedTemplate = env.getDeclaredTemplate(node.optName);

  if (!relatedTemplate)
    return execInfo(
      ResultType.KnowUndeclared,
      node.optName + " has not declared"
    );

  let res = fixFreeVarsAndCallHandlerFunc(env, node, _pushNewOpt, [node]);

  if (_isNotResultTypeTrue(res)) return res;

  res = fixFreeVarsAndCallHandlerFunc(
    env,
    node,
    _pushNewOpt,
    relatedTemplate.onlyIfExprs.filter((v) => {
      if (v instanceof CallOptNode) return true;
      else return false;
    })
  );

  return execInfo(ResultType.KnowTrue);
}

function fixFreeVarsAndCallHandlerFunc(
  env: LiTeXEnv,
  fixedNode: CallOptNode, // the fullCallOpt, including params of father opts. 'this' is in the lowest opt of the CallOpt.
  doWhenFreeVarsAreFixed: (
    env: LiTeXEnv,
    fixedParams: string[][],
    relatedTemplate: TemplateNode,
    FixedTemplates?: CallOptNode[]
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
  env.newSymbolsFactsPair(newParams, relatedTemplate);
  return execInfo(ResultType.True);
  // return relatedTemplate.newFact(env, makeTemplateNodeFact(newParams));
};

const _checkOpt = (
  env: LiTeXEnv,
  newParams: string[][],
  relatedTemplate: TemplateNode
) => {
  return env.symbolsFactsPairIsTrue(newParams, relatedTemplate)
    ? execInfo(ResultType.True)
    : execInfo(ResultType.Unknown);
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
    for (const paramGroup of optParams as string[][]) {
      if (env.varsAreNotDeclared(paramGroup)) {
        return false;
      }
    }
  } else {
    // Handle 1D array case
    return !env.varsAreNotDeclared(optParams as string[]);
  }

  return true;
}

function _isNotResultTypeTrue(res: ExecInfo): Boolean {
  if (res.type === ResultType.True) return false;
  else return true;
}

export const _VarsAreNotDeclared = (fact: TemplateNodeFact) =>
  execInfo(
    ResultType.Error,
    `Not all of referred symbols ${fact.params} are declared.`
  );

function _allStartWithAsterisk(arr: string[][]): boolean {
  return arr.every((subArr) => subArr.every((str) => str.startsWith("*")));
}

//! know everything not done
function yaKnowExec(env: LiTeXEnv, node: KnowNode | LetNode): ExecInfo {
  try {
    let facts: CanBeKnownNode[] = [];
    let isKnowEverything: Boolean = false;
    let res: ExecInfo = { type: ResultType.Error, message: "" };

    if (node.type === LiTexNodeType.KnowNode) {
      facts = (node as KnowNode).facts;
      isKnowEverything = (node as KnowNode).isKnowEverything;
    } else if (node.type === LiTexNodeType.LetNode) {
      facts = (node as LetNode).properties;
    }

    for (const fact of facts) {
      switch (fact.type) {
        case LiTexNodeType.CallOptNode:
          if (isKnowEverything)
            res = yaKnowEverythingCallOptExec(env, fact as CallOptNode);
          else res = yaKnowCallOptExec(env, fact as CallOptNode);
          break;
        case LiTexNodeType.DefNode:
        case LiTexNodeType.InferNode: {
          res = templateDeclExec(env, fact as TemplateNode);
          if (isKnowEverything) {
            res = yaKnowEverythingCallOptExec(
              env,
              CallOptNode.create((fact as TemplateNode).declOptName, [
                (fact as TemplateNode).freeVars,
              ])
            );
          } else {
            res = yaKnowCallOptExec(
              env,
              CallOptNode.create((fact as TemplateNode).declOptName, [
                (fact as TemplateNode).freeVars,
              ])
            );
          }
          break;
        }
      }
      if (!execInfoIsTrue(res)) return res;
    }

    return execInfo(ResultType.KnowTrue);
  } catch (error) {
    catchRuntimeError(env, error, "know");
    return execInfo(ResultType.KnowError);
  }
}

function yaKnowEverythingCallOptExec(
  env: LiTeXEnv,
  fact: CallOptNode
): ExecInfo {
  let res: ExecInfo = { type: ResultType.Error, message: "" };
  res = yaKnowCallOptExec(env, fact);

  const template = env.getDeclaredTemplate(fact as CallOptNode);
  if (!template)
    throw Error(`${(fact as CallOptNode).optName} has not been declared.`);

  let mapping = template.fix(fact);
  if (!mapping) return execInfo(ResultType.KnowError);

  template.emitOnlyIfs(env, mapping);
  let noErr = template.emitRequirements(env, mapping);
  if (!noErr) return execInfo(ResultType.Error, "calling undefined operator.");

  if (_isNotResultTypeTrue(res)) return res;

  return execInfo(ResultType.KnowTrue);
}

function yaKnowCallOptExec(env: LiTeXEnv, node: CallOptNode): ExecInfo {
  let relatedTemplate = env.getDeclaredTemplate(node);

  if (!relatedTemplate)
    return execInfo(
      ResultType.KnowUndeclared,
      node.optName + " has not declared"
    );

  //! THE CLASSICAL WAY OF TRANSFORMING FREE VAR INTO FIXED AND EMIT
  env.newSymbolsFactsPair(
    node.optParams,
    env.getDeclaredTemplate(node) as TemplateNode,
    node.requirements
  );
  let mapping = relatedTemplate.fix(node);
  if (!mapping) return execInfo(ResultType.KnowError);
  // let res = relatedTemplate.emit(env, mapping, );

  let allRequirementsAreSatisfied = relatedTemplate.requirementsSatisfied(
    env,
    mapping
  );

  //! If all the requirements of this template is satisfied, then facts are emitted.
  if (allRequirementsAreSatisfied) {
    for (let onlyIf of relatedTemplate.onlyIfExprs) {
      if (onlyIf instanceof CallOptNode) {
        let tmp = env.getDeclaredTemplate(onlyIf);
        if (!tmp) return execInfo(ResultType.Error);
        tmp.emit(env, mapping, node.optParams);
      }
    }
  }

  return execInfo(ResultType.KnowTrue);
  // else return execInfo(ResultType.KnowError, res.message);
}

// export function emitByFixingFreeVars(
//   env: LiTeXEnv,
//   mapping: Map<string, string>,
//   callOptParams: CallOptNode | string[][]
// ) {
//   if (callOptParams instanceof CallOptNode) {
//     callOptParams = callOptParams.optParams;
//   }

// }

function yaProveExec(env: LiTeXEnv, node: YAProveNode): ExecInfo {
  const relatedTemplate = env.getDeclaredTemplate(node.templateNames.join(":"));
  if (!relatedTemplate)
    return execInfo(
      ResultType.ProveError,
      `${node.templateNames.join(":")} is not declared.`
    );
  env = new LiTeXEnv(env);

  // introduce vars into new env
  for (let l of node.freeVars) {
    for (let freeVar of l) {
      if (freeVar.startsWith("*")) continue;
      else if (freeVar.startsWith("#")) {
        return execInfo(
          ResultType.ProveError,
          "parameters in requirement should not start with #"
        );
      } else {
        let res = env.newVar(freeVar);
        if (!res)
          return execInfo(
            ResultType.ProveError,
            "two parameters have the same name."
          );
      }
    }
  }

  // emit or check requirements of template on vars
  for (let [index, curParams] of node.freeVars.entries()) {
    // getName
    let optName = node.templateNames[0];
    for (let i = 1; i <= index; i++) {
      optName += ":" + node.freeVars[i];
    }

    // fixedParams
    let params = node.freeVars.slice(0, index + 1);
    const allStartWithAsterisk = _allStartWithAsterisk(params);
    params.map((e) =>
      e.map((s) => {
        s.startsWith("*") ? s.slice(1) : s;
      })
    );

    if (allStartWithAsterisk) {
      /* check requirements */
      const res = callOptExec(env, CallOptNode.create(optName, params));
      if (!execInfoIsTrue(res))
        return execInfo(ResultType.Error, `${optName} is not true`);
    } else {
      /* emit requirements: copy some code from knowEverything */
      const fact = CallOptNode.create(optName, params);

      const template = env.getDeclaredTemplate(fact as CallOptNode);
      if (!template)
        throw Error(`${(fact as CallOptNode).optName} has not been declared.`);

      let mapping = template.fix(fact);
      if (!mapping) return execInfo(ResultType.KnowError);

      template.emitOnlyIfs(env, mapping);
      let noErr = template.emitRequirements(env, mapping);
      if (!noErr)
        return execInfo(ResultType.Error, "calling undefined operator.");
    }
  }

  let res: ExecInfo = execInfo(ResultType.ProveError);
  let onlyIfsThatNeedsCheck = [...relatedTemplate.onlyIfExprs];

  for (let onlyIfCallOpts of node.onlyIfExprs) {
    if (onlyIfCallOpts instanceof CallOptsNode) {
      for (let onlyIf of (onlyIfCallOpts as CallOptsNode).nodes) {
        processOnlyIfCallOpt(onlyIf);
      }
    } else {
      processOnlyIfCallOpt(onlyIfCallOpts as CallOptNode);
    }
  }

  if (onlyIfsThatNeedsCheck.length === 0) return execInfo(ResultType.ProveTrue);
  else
    return execInfo(
      ResultType.ProveError,
      "not all onlyIfs in template are satisfied."
    );

  function processOnlyIfCallOpt(onlyIf: CallOptNode) {
    res = nodeExec(env, onlyIf);
    if (onlyIf instanceof CallOptNode) {
      for (let i = 0; i < onlyIfsThatNeedsCheck.length; i++) {
        let onlyIfThatNeedsCheck = onlyIfsThatNeedsCheck[i];
        let isTrue = fixFreeVarsAndCallHandlerFunc(env, onlyIf, _checkOpt, [
          onlyIfThatNeedsCheck,
        ]);
        if (execInfoIsTrue(isTrue)) {
          fixFreeVarsAndCallHandlerFunc(env, onlyIf, _pushNewOpt, [
            onlyIfThatNeedsCheck,
          ]);
          onlyIfsThatNeedsCheck.splice(i, 1);
          i--;
        }
      }
    }
  }
}
