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
  KnowEverythingTrue,
  KnowEverythingError,
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
  [ResultType.KnowEverythingError]: "know_everything: error",
  [ResultType.KnowEverythingTrue]: "know_everything: true",
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

export function handleRuntimeError(
  env: LiTeXEnv,
  type: ResultType,
  m: string = ""
): ExecInfo {
  env.pushNewError(resultTypeMap[type] + ": " + m);
  return execInfo(type, m);
}

export const execInfo = (t: ResultType, s: string = "") => {
  return { type: t, message: s };
};
export type ExecInfo = { type: ResultType; message: string };

export function nodeExec(env: LiTeXEnv, node: LiTeXNode): ExecInfo {
  try {
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
    return execInfo(ResultType.Error, "Stmt");
  } catch (error) {
    return handleRuntimeError(env, ResultType.Error, "Stmt");
  }
}

function letExec(env: LiTeXEnv, node: LetNode): ExecInfo {
  try {
    // Check ofr duplicate variable declarations
    const notDeclared = node.vars.filter((v) => env.declaredVars.includes(v));
    if (!notDeclared) {
      return handleRuntimeError(
        env,
        ResultType.LetError,
        `Error: Variable(s) ${node.vars.join(", ")} already declared in this scope.`
      );
    }

    env.declaredVars = env.declaredVars.concat(node.vars) as string[];

    for (let i = 0; i < node.properties.length; i++) {
      let info = yaKnowCallOptExec(env, node.properties[i]);
      if (!execInfoIsTrue(info))
        return handleRuntimeError(env, ResultType.KnowError, "");
    }

    return execInfo(ResultType.LetTrue);
  } catch (error) {
    return handleRuntimeError(env, ResultType.LetError, "let");
  }
}

function callOptsExec(env: LiTeXEnv, node: CallOptsNode): ExecInfo {
  try {
    for (const fact of (node as CallOptsNode).nodes) {
      let info = callOptExec(env, fact as CallOptNode);
      if (!execInfoIsTrue(info))
        return handleRuntimeError(env, ResultType.Error, "");
    }
    return execInfo(ResultType.True);
  } catch (error) {
    return handleRuntimeError(env, ResultType.Error, "call operators");
  }
}

function callOptExec(env: LiTeXEnv, node: CallOptNode): ExecInfo {
  try {
    const builtinFunc = LiTeXBuiltinKeywords[node.optName];
    if (builtinFunc) {
      return builtinFunc(env, node);
    }

    const relatedTemplate = env.getDeclaredTemplate(node);
    if (!relatedTemplate)
      return handleRuntimeError(
        env,
        ResultType.False,
        node.optName + " is not declared."
      );

    // check itself
    let isTrue: Boolean = env.symbolsFactsPairIsTrue(
      node.optParams,
      relatedTemplate
    );

    if (!isTrue)
      return handleRuntimeError(
        env,
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

    // emit
    relatedTemplate.emitOnlyIfs(env, mapping);

    return execInfo(
      ResultType.DefTrue,
      `${node.optName} itself and its requirements are all satisfied.`
    );
  } catch (error) {
    return handleRuntimeError(env, ResultType.Error, "call operator");
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
    return handleRuntimeError(env, ResultType.DefError, "template declaration");
  }
}

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
    return handleRuntimeError(env, ResultType.KnowError, "know");
  }
}

function yaKnowEverythingCallOptExec(
  env: LiTeXEnv,
  fact: CallOptNode
): ExecInfo {
  try {
    let res: ExecInfo = { type: ResultType.Error, message: "" };
    res = yaKnowCallOptExec(env, fact);

    const template = env.getDeclaredTemplate(fact as CallOptNode);
    if (!template)
      throw Error(`${(fact as CallOptNode).optName} has not been declared.`);

    let mapping = template.fix(fact);
    if (!mapping) return execInfo(ResultType.KnowError);

    template.emitOnlyIfs(env, mapping);
    let noErr = template.emitRequirements(env, mapping);
    if (!noErr)
      return execInfo(ResultType.Error, "calling undefined operator.");

    if (_isNotResultTypeTrue(res)) return res;

    return execInfo(ResultType.KnowTrue);
  } catch (error) {
    return handleRuntimeError(env, ResultType.KnowEverythingError, "");
  }
}

function yaKnowCallOptExec(env: LiTeXEnv, node: CallOptNode): ExecInfo {
  try {
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
  } catch (error) {
    return handleRuntimeError(env, ResultType.KnowError, "");
  }
}

function yaProveExec(env: LiTeXEnv, node: YAProveNode): ExecInfo {
  try {
    const relatedTemplate = env.getDeclaredTemplate(
      node.templateNames.join(":")
    );
    if (!relatedTemplate)
      return execInfo(
        ResultType.ProveError,
        `${node.templateNames.join(":")} is not declared.`
      );
    const originalEnv = env;
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

    // Emit and check requirements from template declaration and proveNode
    for (let [index, curParams] of node.freeVars.entries()) {
      // Handle template requirements
      let optName = node.templateNames[0];
      for (let i = 1; i <= index; i++) {
        optName += ":" + node.freeVars[i];
      }

      let result: { type: ResultType; message: string } | null;
      // let params = node.freeVars.slice(0, index + 1);
      // let result = handleRequirements(env, optName, params);
      // if (result) return result;

      // Handle extra requirements in proveNode
      if (node.requirements[index].length > 0) {
        for (let requirement of node.requirements[index]) {
          result = handleRequirements(
            env,
            requirement.optName,
            requirement.optParams,
            true
          );
          if (result) return result;
        }
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
    if (onlyIfsThatNeedsCheck.length === 0) {
      /** If prove is true, then emit new fact. */

      /** FixedVars */
      const fixedVars = [];
      for (let l of node.freeVars) {
        const vl = [];
        for (let v of l) {
          if (v.startsWith("*")) vl.push(v.slice(1));
          else vl.push("#" + v);
        }
        fixedVars.push(vl);
      }

      const TName = node.templateNames.join(":");
      const relatedT = env.getDeclaredTemplate(TName);
      if (!relatedT)
        return execInfo(ResultType.Error, `${TName} has not declared.`);

      /** Fix Prove requirements */
      const requirements: CallOptNode[][] = [];
      for (let l of node.requirements) {
        const vl: CallOptNode[] = [];
        for (let req of l as CallOptNode[]) {
          /**  Fix freeVars in a single requirement */
          const fixedFreeVarsArr: string[][] = [];
          for (let freeVars of node.freeVars) {
            const fixedFreeVars: string[] = [];
            for (let s of freeVars) {
              if (s.startsWith("*")) fixedFreeVars.push(s.slice(1));
              else fixedFreeVars.push("#" + s);
            }
            fixedFreeVarsArr.push(fixedFreeVars);
          }

          vl.push(CallOptNode.create(req.optName, fixedFreeVarsArr));
        }

        requirements.push(vl);
      }

      /** Fix template requirements */
      const mapping = relatedT.fix(fixedVars);
      for (let [index, opt] of node.templateNames.entries()) {
        let name = node.templateNames[0];
        for (let i = 1; i < index; i++) name += ":" + node.templateNames[i];
        const curT = env.getDeclaredTemplate(name);
        if (!curT) return execInfo(ResultType.Error);

        /** new requirement */
        for (let req of curT?.requirements as CallOptNode[]) {
          /** get name of current requirement */
          const fixedFreeVarsArr: string[][] = [];
          for (let freeVars of req.optParams) {
            const fixedFreeVars: string[] = [];
            for (let s of freeVars) {
              fixedFreeVars.push(mapping?.get(s) as string);
            }
            fixedFreeVarsArr.push(fixedFreeVars);
          }

          requirements[index].push(
            CallOptNode.create(req.optName, fixedFreeVarsArr)
          );
        }
      }

      originalEnv.newSymbolsFactsPair(fixedVars, relatedT, requirements);

      return execInfo(ResultType.ProveTrue);
    } else
      return execInfo(
        ResultType.ProveError,
        "not all onlyIfs in template are satisfied."
      );

    function processOnlyIfCallOpt(onlyIf: CallOptNode) {
      res = nodeExec(env, onlyIf);
      if (onlyIf instanceof CallOptNode) {
        for (let i = 0; i < onlyIfsThatNeedsCheck.length; i++) {
          let checkedOpt = onlyIfsThatNeedsCheck[i] as CallOptNode;
          let relatedT = env.getDeclaredTemplate(checkedOpt) as TemplateNode;
          let isTrue = env.symbolsFactsPairIsTrue(
            checkedOpt.optParams,
            relatedT
          );

          if (isTrue) {
            env.newSymbolsFactsPair(checkedOpt.optParams, relatedT);
            onlyIfsThatNeedsCheck.splice(i, 1);
            i--;
          }
        }
      }
    }

    function handleRequirements(
      env: LiTeXEnv,
      optName: string,
      params: string[][],
      isExtraRequirement = false
    ) {
      const allStartWithAsterisk = _allStartWithAsterisk(params);
      params = params.map((e) =>
        e.map((s) => (s.startsWith("*") ? s.slice(1) : s))
      );

      if (allStartWithAsterisk) {
        /* check requirements */
        const res = callOptExec(env, CallOptNode.create(optName, params));
        if (!execInfoIsTrue(res)) {
          return execInfo(ResultType.Error, `${optName} is not true`);
        }
      } else {
        /* emit requirements */
        const fact = CallOptNode.create(optName, params);
        const template = env.getDeclaredTemplate(fact);
        if (!template) {
          throw Error(`${optName} has not been declared.`);
        }

        let mapping = template.fix(fact);
        if (!mapping) return execInfo(ResultType.KnowError);

        if (isExtraRequirement) {
          env.newSymbolsFactsPair(params, template);
        } else {
          let noErr = template.emitRequirements(env, mapping);
          if (!noErr) {
            return execInfo(ResultType.Error, "calling undefined operator.");
          }
        }
      }

      return null; // No error
    }
  } catch (error) {
    return handleRuntimeError(env, ResultType.ProveError, "");
  }
}
