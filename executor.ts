import { findIndex } from "lodash";
import {
  CallOptNode,
  CallOptsNode,
  KnowNode,
  LiTeXNode,
  LiTexNodeType,
  LetNode,
  CanBeKnownNode,
  TemplateNode,
  YAProveNode,
  HaveNode,
} from "./ast";
import { LiTeXBuiltinKeywords } from "./builtins";
import { LiTeXKeywords } from "./common";
import { LiTeXEnv } from "./env";

export enum ResultType {
  True, // not only used as True for callInferExec, but also as a generic type passed between subFunctions.
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
  ExistError,
  ExistTrue,
}

export const ResultTypeMap: { [key in ResultType]: string } = {
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
  [ResultType.ExistError]: "exist: error",
  [ResultType.ExistTrue]: "exist: true",
};

export function execInfoIsTrue(res: ExecInfo) {
  return [
    ResultType.True,
    ResultType.KnowTrue,
    ResultType.DefTrue,
    ResultType.HaveTrue,
    ResultType.LetTrue,
    ResultType.ProveTrue,
    ResultType.KnowEverythingTrue,
    ResultType.ExistTrue,
  ].includes(res.type);
}

export function handleRuntimeError(
  env: LiTeXEnv,
  type: ResultType,
  message: string = ""
): ExecInfo {
  env.pushNewError(ResultTypeMap[type] + ": " + message);
  return execInfo(type, message);
}

export const execInfo = (t: ResultType, s: string = "") => {
  return { type: t, message: s };
};
export type ExecInfo = { type: ResultType; message: string };
export const ErrorExecInfo = { type: ResultType.Error, message: "" };

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
      case LiTexNodeType.HaveNode:
        return haveExec(env, node as HaveNode);
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
        return handleRuntimeError(env, ResultType.LetError, info.message);
    }

    return execInfo(ResultType.LetTrue);
  } catch (error) {
    return handleRuntimeError(env, ResultType.LetError, "let");
  }
}

function callOptsExec(env: LiTeXEnv, node: CallOptsNode): ExecInfo {
  try {
    const whatIsTrue: string[] = [];
    for (const fact of (node as CallOptsNode).nodes) {
      const relatedTemplate = env.getDeclaredTemplate(fact as CallOptNode);
      if (!relatedTemplate)
        return handleRuntimeError(
          env,
          ResultType.Error,
          `${fact.optName} is not declared.`
        );
      let info: ExecInfo = ErrorExecInfo;
      switch (relatedTemplate.type) {
        case LiTexNodeType.DefNode:
          info = callDefExec(env, fact, relatedTemplate);
          break;
        case LiTexNodeType.ExistNode:
          info = callExistExec(env, fact, relatedTemplate);
          break;
        case LiTexNodeType.InferNode:
          info = callInferExec(env, fact, relatedTemplate);
          break;
      }
      if (info.type === ResultType.Unknown || info.type === ResultType.False) {
        return info;
      }
      if (!execInfoIsTrue(info))
        return handleRuntimeError(env, ResultType.Error, "");
      whatIsTrue.push(`${fact.optName} ${fact.optParams}`);
    }
    return execInfo(ResultType.True, whatIsTrue.join(";"));
  } catch (error) {
    return handleRuntimeError(env, ResultType.Error, "call operators");
  }
}

function callInferExec(
  env: LiTeXEnv,
  node: CallOptNode,
  relatedTemplate: TemplateNode | undefined = undefined
): ExecInfo {
  try {
    const builtinFunc = LiTeXBuiltinKeywords[node.optName];
    if (builtinFunc) {
      return builtinFunc(env, node);
    }

    if (!relatedTemplate) relatedTemplate = env.getDeclaredTemplate(node);

    if (!relatedTemplate)
      return handleRuntimeError(
        env,
        ResultType.False,
        node.optName + " is not declared."
      );

    // if (relatedTemplate?.type === LiTexNodeType.ExistNode) {
    //   return callExistExec(env, node as CallOptNode);
    // } else if (relatedTemplate.type === LiTexNodeType.DefNode) {
    //   return callDefExec(env, node as CallOptNode);
    // }

    // check itself
    let isTrue: Boolean = env.isStoredTrueFact(node.optParams, relatedTemplate);

    if (!isTrue)
      return handleRuntimeError(
        env,
        ResultType.Unknown,
        `${node.optName} itself is not satisfied.`
      );

    // check all requirements
    const mapping = relatedTemplate.fix(node);
    if (!mapping) return handleRuntimeError(env, ResultType.Error);
    isTrue = relatedTemplate.requirementsSatisfied(env, mapping);
    if (!isTrue)
      return handleRuntimeError(
        env,
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

function templateDeclExec(env: LiTeXEnv, node: TemplateNode): ExecInfo {
  try {
    const declaredTemplates = env.declaredTemplates as Map<
      string,
      TemplateNode
    >;

    // Check if the template name already exists
    if (!node.isRedefine && declaredTemplates.has(node.declOptName)) {
      throw new Error(
        `Template '${node.declOptName}' has already been declared. Duplicate declarations are not allowed.`
      );
    }

    if (LiTeXKeywords.includes(node.declOptName)) {
      throw new Error(`Template '${node.declOptName}' is LiTeX keyword.`);
    }

    // If not already declared, set the new template
    declaredTemplates.set(node.declOptName, node);

    // move templates(pure, questionMark) from node.onlyIfs to node.declaredTemplates
    let res = node.initDeclaredTemplates(env);
    if (!execInfoIsTrue(res))
      return handleRuntimeError(env, ResultType.DefError);

    switch (node.type) {
      case LiTexNodeType.DefNode:
        return execInfo(ResultType.DefTrue, "def");
      case LiTexNodeType.ExistNode:
        return execInfo(ResultType.DefTrue, "exist");
      case LiTexNodeType.InferNode:
        return execInfo(ResultType.DefTrue, "infer");
    }

    return execInfo(ResultType.Error);
  } catch (error) {
    return handleRuntimeError(
      env,
      ResultType.DefError,
      `Template declaration error: ${(error as Error).message}`
    );
  }
}

function yaKnowExec(env: LiTeXEnv, node: KnowNode): ExecInfo {
  try {
    let facts: CanBeKnownNode[] = [];
    let isKnowEverything: Boolean = false;
    let res: ExecInfo = { type: ResultType.Error, message: "" };

    if (node.type === LiTexNodeType.KnowNode) {
      facts = (node as KnowNode).facts;
      isKnowEverything = (node as KnowNode).isKnowEverything;
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

    if (!execInfoIsTrue(res)) return res;

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
    env.newStoredFact(
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

      originalEnv.newStoredFact(fixedVars, relatedT, requirements);

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
          let isTrue = env.isCallOptTrue(checkedOpt);

          if (isTrue) {
            env.newCallOptFact(checkedOpt);
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
      const allStartWithAsterisk = params.every((subArr) =>
        subArr.every((str) => str.startsWith("*"))
      );
      params = params.map((e) =>
        e.map((s) => (s.startsWith("*") ? s.slice(1) : s))
      );

      if (allStartWithAsterisk) {
        /* check requirements */
        const res = callInferExec(env, CallOptNode.create(optName, params));
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
          env.newStoredFact(params, template);
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

function haveExec(env: LiTeXEnv, node: HaveNode): ExecInfo {
  try {
    /** If a variable is not declared, then declare it. If declared, bind new properties to it  */
    const notDeclared = node.params.filter((v) => env.declaredVars.includes(v));
    if (!notDeclared) {
      env.declareNewVar(notDeclared);
    }

    const optParamsArr = fixFree(env, node.opt, false, true);
    if (optParamsArr === undefined)
      return handleRuntimeError(env, ResultType.HaveError);
    else {
      for (let strArrArr of optParamsArr.req) {
        env.newCallOptFact(
          CallOptNode.create(strArrArr.name, strArrArr.params)
        );
      }
    }

    return execInfo(ResultType.HaveTrue);
  } catch (error) {
    return handleRuntimeError(env, ResultType.HaveError);
  }
}

function _fixFreesUsingMap(
  mapping: Map<string, string>,
  freeArrArr: string[][]
): string[][] | undefined {
  const fixedArrArr: string[][] = [];
  for (let freeArr of freeArrArr) {
    const arr: string[] = [];
    for (let s of freeArr) {
      const fixedS = mapping.get(s);
      if (!fixedS) return undefined;
      arr.push(fixedS);
    }
    fixedArrArr.push(arr);
  }
  return fixedArrArr;
}

type OptParamsType = { name: string; params: string[][] };
type FixFreeType = {
  onlyIf: OptParamsType[];
  req: OptParamsType[];
};

// Main Helper Function
//? Many executor function can be refactored using fixFree
function fixFree(
  env: LiTeXEnv,
  opt: CallOptNode,
  fixOnlyIf: Boolean = false,
  fixReq: Boolean = false,
  relatedTemplate: TemplateNode | undefined = undefined
): FixFreeType | undefined {
  if (!relatedTemplate) env.getDeclaredTemplate(opt);
  const result = {
    onlyIf: [] as OptParamsType[],
    req: [] as OptParamsType[],
  };

  if (!relatedTemplate) {
    handleRuntimeError(env, ResultType.HaveError, "exist not declared");
    return undefined;
  }

  const mapping = relatedTemplate?.fix(opt);
  if (!mapping) {
    handleRuntimeError(env, ResultType.HaveError, "calling undeclared symbol.");
    return undefined;
  }

  if (fixReq) {
    const optParamsArr: OptParamsType[] = [];
    for (let curOpt of relatedTemplate.requirements as CallOptNode[]) {
      const fixedArrArr = _fixFreesUsingMap(mapping, curOpt.optParams);
      if (!fixedArrArr) {
        handleRuntimeError(env, ResultType.HaveError);
        return undefined;
      }
      optParamsArr.push({ name: curOpt.optName, params: fixedArrArr });
    }
    result.req = optParamsArr;
  }

  if (fixOnlyIf) {
    const optParamsArr: OptParamsType[] = [];
    for (let curOpt of relatedTemplate.onlyIfExprs as CallOptNode[]) {
      const fixedArrArr = _fixFreesUsingMap(mapping, curOpt.optParams);
      if (!fixedArrArr) {
        handleRuntimeError(env, ResultType.HaveError);
        return undefined;
      }
      optParamsArr.push({ name: curOpt.optName, params: fixedArrArr });
    }
    result.onlyIf = optParamsArr;
  }

  return result;
}

function callExistExec(
  env: LiTeXEnv,
  node: CallOptNode,
  relatedTemplate: TemplateNode
): ExecInfo {
  try {
    // const relatedTemplate = env.getDeclaredTemplate(node);
    // if (!relatedTemplate)
    //   return handleRuntimeError(
    //     env,
    //     ResultType.Error,
    //     `${node.optName} has not declared.`
    //   );

    const fixedRequirements = fixFree(env, node, false, true)?.req;
    if (fixedRequirements === undefined)
      return handleRuntimeError(
        env,
        ResultType.Error,
        `Invalid invocation of ${node.optName}.`
      );

    for (let fixedReq of fixedRequirements) {
      const tmp = env.getDeclaredTemplate(fixedReq.name);
      if (!tmp)
        return handleRuntimeError(
          env,
          ResultType.Error,
          `${findIndex.name} has not declared.`
        );
      if (!env.isStoredTrueFact(fixedReq.params, tmp))
        return execInfo(ResultType.Unknown);
    }

    return execInfo(ResultType.True);
  } catch (error) {
    return handleRuntimeError(env, ResultType.Error);
  }
}

function callDefExec(
  env: LiTeXEnv,
  node: CallOptNode,
  relatedTemplate: TemplateNode
): ExecInfo {
  try {
    // check left(i.e. the opt itself)
    let leftIsTrue: Boolean = env.isStoredTrueFact(
      node.optParams,
      relatedTemplate
    );

    if (leftIsTrue) {
      const fixedRequirements = fixFree(
        env,
        node,
        false,
        true,
        relatedTemplate
      )?.req;
      if (!fixedRequirements)
        return handleRuntimeError(
          env,
          ResultType.Error,
          `Invalid invocation of ${node.optName}.`
        );
      for (let fixedReq of fixedRequirements) {
        const tmp = env.getDeclaredTemplate(fixedReq.name);
        if (!tmp)
          return handleRuntimeError(
            env,
            ResultType.Error,
            `${findIndex.name} has not declared.`
          );
        env.newStoredFact(fixedReq.params, tmp);
      }
    }

    let rightIsTrue: Boolean = false;
    const mapping = relatedTemplate.fix(node);
    if (!mapping) return handleRuntimeError(env, ResultType.Error);
    rightIsTrue = relatedTemplate.requirementsSatisfied(env, mapping);
    if (!rightIsTrue) return execInfo(ResultType.Unknown);
    else {
      env.newCallOptFact(node);
    }
    return execInfo(ResultType.True);
  } catch (error) {
    return handleRuntimeError(env, ResultType.DefError);
  }
}
