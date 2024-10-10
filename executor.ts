import { findIndex } from "lodash";
import {
  CallOptNode,
  CallOptsNode,
  KnowNode,
  LiTeXNode,
  LiTeXNodeType,
  LetNode,
  CanBeKnownNode,
  TemplateNode,
  YAProveNode,
  HaveNode,
  ExistNode,
  ImpliesFactNode,
} from "./ast";
import { LiTeXBuiltinKeywords } from "./builtins";
import { LiTeXKeywords } from "./common";
import { LiTeXEnv } from "./env";

export enum RType {
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

export const RTypeMap: { [key in RType]: string } = {
  [RType.Error]: "error",
  [RType.False]: "check: false",
  [RType.True]: "check: true",
  [RType.Unknown]: "check: unknown",
  [RType.KnowTrue]: "know: true",
  [RType.DefTrue]: "def: true",
  [RType.KnowError]: "know: error",
  [RType.DefError]: "def: error",
  [RType.KnowUndeclared]: "know: undeclared opt",
  [RType.HaveError]: "have: error",
  [RType.HaveTrue]: "have: true",
  [RType.LetError]: "let: error",
  [RType.LetTrue]: "let: true",
  [RType.ProveError]: "prove: error",
  [RType.ProveTrue]: "prove: true",
  [RType.KnowEverythingError]: "know_everything: error",
  [RType.KnowEverythingTrue]: "know_everything: true",
  [RType.ExistError]: "exist: error",
  [RType.ExistTrue]: "exist: true",
};

export function execInfoIsTrue(res: ExecInfo) {
  return [
    RType.True,
    RType.KnowTrue,
    RType.DefTrue,
    RType.HaveTrue,
    RType.LetTrue,
    RType.ProveTrue,
    RType.KnowEverythingTrue,
    RType.ExistTrue,
  ].includes(res.type);
}

export function hRunErr(
  env: LiTeXEnv,
  type: RType,
  message: string = ""
): ExecInfo {
  env.pushNewError(RTypeMap[type] + ": " + message);
  return execInfo(type, message);
}

export const execInfo = (t: RType, s: string = "") => {
  return { type: t, message: s };
};
export type ExecInfo = { type: RType; message: string };
export const ErrorExecInfo = { type: RType.Error, message: "" };

export function nodeExec(env: LiTeXEnv, node: LiTeXNode): ExecInfo {
  try {
    switch (node.type) {
      case LiTeXNodeType.DefNode:
      case LiTeXNodeType.InferNode:
      case LiTeXNodeType.ExistNode:
        return templateDeclExec(env, node as TemplateNode);
      case LiTeXNodeType.KnowNode:
        return yaKnowExec(env, node as KnowNode);
      case LiTeXNodeType.CallOptsNode:
        return callOptsExec(env, node as CallOptsNode);
      case LiTeXNodeType.LetNode:
        return letExec(env, node as LetNode);
      case LiTeXNodeType.ProofNode:
        return execInfo(RType.True);
      // return proveExec(env, node as YAProveNode);
      case LiTeXNodeType.HaveNode:
        return haveExec(env, node as HaveNode);
    }
    return execInfo(RType.Error, "Stmt");
  } catch (error) {
    return hRunErr(env, RType.Error, "Stmt");
  }
}

function letExec(env: LiTeXEnv, node: LetNode): ExecInfo {
  try {
    // Check ofr duplicate variable declarations
    const notDeclared = node.vars.filter((v) => env.declaredVars.includes(v));
    if (!notDeclared) {
      return hRunErr(
        env,
        RType.LetError,
        `Error: Variable(s) ${node.vars.join(", ")} already declared in this scope.`
      );
    }

    env.declaredVars = env.declaredVars.concat(node.vars) as string[];

    for (let i = 0; i < node.properties.length; i++) {
      let info = yaKnowCallOptExec(env, node.properties[i]);
      if (!execInfoIsTrue(info))
        return hRunErr(env, RType.LetError, info.message);
    }

    return execInfo(RType.LetTrue);
  } catch (error) {
    return hRunErr(env, RType.LetError, "let");
  }
}

function callOptsExec(env: LiTeXEnv, node: CallOptsNode): ExecInfo {
  try {
    const whatIsTrue: string[] = [];
    for (const fact of (node as CallOptsNode).nodes) {
      const relatedTemplate = env.getDeclaredTemplate(fact as CallOptNode);
      if (!relatedTemplate)
        return hRunErr(env, RType.Error, `${fact.optName} is not declared.`);
      let info: ExecInfo = ErrorExecInfo;
      switch (relatedTemplate.type) {
        case LiTeXNodeType.ExistNode:
          info = callDefExec(env, fact, relatedTemplate, true);
          break;
        case LiTeXNodeType.DefNode:
          info = callDefExec(env, fact, relatedTemplate);
          break;
        case LiTeXNodeType.InferNode:
          info = callInferExec(env, fact, relatedTemplate);
          break;
      }
      if (info.type === RType.Unknown || info.type === RType.False) {
        return info;
      }
      if (!execInfoIsTrue(info)) return hRunErr(env, RType.Error, "");
      whatIsTrue.push(`${fact.optName} ${fact.optParams}`);
    }
    return execInfo(RType.True, whatIsTrue.join(";"));
  } catch (error) {
    return hRunErr(env, RType.Error, "call operators");
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
      return hRunErr(env, RType.False, node.optName + " is not declared.");

    // if (relatedTemplate?.type === LiTeXNodeType.ExistNode) {
    //   return callExistExec(env, node as CallOptNode);
    // } else if (relatedTemplate.type === LiTeXNodeType.DefNode) {
    //   return callDefExec(env, node as CallOptNode);
    // }

    // check itself
    let isTrue: Boolean | undefined = env.isStoredTrueFact(
      node.optParams,
      relatedTemplate
    );

    if (!isTrue)
      return hRunErr(
        env,
        RType.Unknown,
        `${node.optName} itself is not satisfied.`
      );

    // check all requirements
    isTrue = checkFree(env, node, relatedTemplate, false, true);

    // const mapping = relatedTemplate.fix(node);
    // if (!mapping) return hRunErr(env, RType.Error);
    // isTrue = relatedTemplate.requirementsSatisfied(env, mapping);

    if (!isTrue)
      return hRunErr(
        env,
        RType.Unknown,
        `${node.optName} itself is true while its requirements are not satisfied.`
      );

    // emit
    emitFree(env, node, relatedTemplate, true, false);
    // relatedTemplate.emitOnlyIfs(env, mapping);

    return execInfo(
      RType.DefTrue,
      `${node.optName} itself and its requirements are all satisfied.`
    );
  } catch (error) {
    return hRunErr(env, RType.Error, "call operator");
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
    if (!execInfoIsTrue(res)) return hRunErr(env, RType.DefError);

    switch (node.type) {
      case LiTeXNodeType.DefNode:
        return execInfo(RType.DefTrue, "def");
      case LiTeXNodeType.ExistNode:
        return execInfo(RType.DefTrue, "exist");
      case LiTeXNodeType.InferNode:
        return execInfo(RType.DefTrue, "infer");
    }

    return execInfo(RType.Error);
  } catch (error) {
    return hRunErr(
      env,
      RType.DefError,
      `Template declaration error: ${(error as Error).message}`
    );
  }
}

function yaKnowExec(env: LiTeXEnv, node: KnowNode): ExecInfo {
  try {
    let facts: CanBeKnownNode[] = [];
    let isKnowEverything: Boolean = false;
    let res: ExecInfo = { type: RType.Error, message: "" };

    if (node.type === LiTeXNodeType.KnowNode) {
      facts = (node as KnowNode).facts;
      isKnowEverything = (node as KnowNode).isKnowEverything;
    }

    for (const fact of facts) {
      switch (fact.type) {
        case LiTeXNodeType.CallOptNode:
          if (isKnowEverything)
            res = yaKnowEverythingCallOptExec(env, fact as CallOptNode);
          else res = yaKnowCallOptExec(env, fact as CallOptNode);
          break;
        case LiTeXNodeType.ImpliesFactNode:
          res = knowImpliesFactExec(env, fact as ImpliesFactNode);
          break;
        case LiTeXNodeType.DefNode:
        case LiTeXNodeType.InferNode: {
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

    return execInfo(RType.KnowTrue);
  } catch (error) {
    return hRunErr(env, RType.KnowError, "know");
  }
}

function yaKnowEverythingCallOptExec(
  env: LiTeXEnv,
  fact: CallOptNode
): ExecInfo {
  try {
    let res: ExecInfo = { type: RType.Error, message: "" };
    res = yaKnowCallOptExec(env, fact);

    const template = env.getDeclaredTemplate(fact as CallOptNode);
    if (!template)
      throw Error(`${(fact as CallOptNode).optName} has not been declared.`);

    emitFree(env, fact, template, true, true);

    // let mapping = template.fix(fact);
    // if (!mapping) return execInfo(RType.KnowError);

    // template.emitOnlyIfs(env, mapping);
    // let noErr = template.emitRequirements(env, mapping);
    // if (!noErr)
    //   return execInfo(RType.Error, "calling undefined operator.");

    // if (!execInfoIsTrue(res)) return res;

    return execInfo(RType.KnowTrue);
  } catch (error) {
    return hRunErr(env, RType.KnowEverythingError, "");
  }
}

function yaKnowCallOptExec(env: LiTeXEnv, node: CallOptNode): ExecInfo {
  try {
    if (
      !node.optParams.every((ls) =>
        ls.every((s) => env.declaredVars.includes(s) || s.startsWith("#"))
      )
    ) {
      return hRunErr(env, RType.KnowError, "symbol not declared.");
    }

    let relatedTemplate = env.getDeclaredTemplate(node);

    if (!relatedTemplate)
      return execInfo(RType.KnowUndeclared, node.optName + " has not declared");

    //! THE CLASSICAL WAY OF TRANSFORMING FREE VAR INTO FIXED AND EMIT
    env.newStoredFact(
      node.optParams,
      env.getDeclaredTemplate(node) as TemplateNode,
      node.requirements
    );

    /** The following lines should be refactored */
    // let rightIsTrue: Boolean = false;
    // const mapping = relatedTemplate.fix(node);
    // if (!mapping) return hRunErr(env, RType.Error);
    // rightIsTrue = relatedTemplate.requirementsSatisfied(env, mapping);

    let rightIsTrue = checkFree(env, node, relatedTemplate, false, true);

    if (!rightIsTrue) return execInfo(RType.Unknown);
    else {
      const res = emitFree(env, node, relatedTemplate, true, false);
      if (!execInfoIsTrue(res)) return res;

      /** All code in else can be abstracted */
      // const fixedRequirements = fixFree(
      //   env,
      //   node,
      //   true,
      //   false,
      //   relatedTemplate
      // )?.onlyIf;
      // if (!fixedRequirements)
      //   return hRunErr(
      //     env,
      //     RType.Error,
      //     `Invalid invocation of ${node.optName}.`
      //   );
      // // emit
      // for (let fixedReq of fixedRequirements) {
      //   const tmp = env.getDeclaredTemplate(fixedReq.name);
      //   if (!tmp)
      //     return hRunErr(
      //       env,
      //       RType.Error,
      //       `${findIndex.name} has not declared.`
      //     );
      //   env.newStoredFact(fixedReq.params, tmp);
      // }
    }

    return execInfo(RType.KnowTrue);
    // else return execInfo(RType.KnowError, res.message);
  } catch (error) {
    return hRunErr(env, RType.KnowError, "");
  }
}

// function proveInferExec(env: LiTeXEnv, node: YAProveNode): ExecInfo {
//   try {
//     const relatedTemplate = env.getDeclaredTemplate(
//       node.templateNames.join(":")
//     );
//     if (!relatedTemplate)
//       return execInfo(
//         RType.ProveError,
//         `${node.templateNames.join(":")} is not declared.`
//       );
//     const originalEnv = env;
//     env = new LiTeXEnv(env);

//     // introduce vars into new env
//     for (let l of node.freeVars) {
//       for (let freeVar of l) {
//         if (freeVar.startsWith("*")) continue;
//         else if (freeVar.startsWith("#")) {
//           return execInfo(
//             RType.ProveError,
//             "parameters in requirement should not start with #"
//           );
//         } else {
//           let res = env.newVar(freeVar);
//           if (!res)
//             return execInfo(
//               RType.ProveError,
//               "two parameters have the same name."
//             );
//         }
//       }
//     }

//     // Emit and check requirements from template declaration and proveNode
//     for (let [index, curParams] of node.freeVars.entries()) {
//       // Handle template requirements
//       let optName = node.templateNames[0];
//       for (let i = 1; i <= index; i++) {
//         optName += ":" + node.freeVars[i];
//       }

//       let result: { type: RType; message: string } | null;
//       // let params = node.freeVars.slice(0, index + 1);
//       // let result = handleRequirements(env, optName, params);
//       // if (result) return result;

//       // Handle extra requirements in proveNode
//       if (node.requirements[index].length > 0) {
//         for (let requirement of node.requirements[index]) {
//           result = handleRequirements(
//             env,
//             requirement.optName,
//             requirement.optParams,
//             true
//           );
//           if (result) return result;
//         }
//       }
//     }

//     let res: ExecInfo = execInfo(RType.ProveError);
//     let onlyIfsThatNeedsCheck = [...relatedTemplate.onlyIfExprs];
//     for (let onlyIfCallOpts of node.onlyIfExprs) {
//       if (onlyIfCallOpts instanceof CallOptsNode) {
//         for (let onlyIf of (onlyIfCallOpts as CallOptsNode).nodes) {
//           processOnlyIfCallOpt(onlyIf);
//         }
//       } else {
//         processOnlyIfCallOpt(onlyIfCallOpts as CallOptNode);
//       }
//     }
//     if (onlyIfsThatNeedsCheck.length === 0) {
//       /** If prove is true, then emit new fact. */

//       /** FixedVars */
//       const fixedVars = [];
//       for (let l of node.freeVars) {
//         const vl = [];
//         for (let v of l) {
//           if (v.startsWith("*")) vl.push(v.slice(1));
//           else vl.push("#" + v);
//         }
//         fixedVars.push(vl);
//       }

//       const TName = node.templateNames.join(":");
//       const relatedT = env.getDeclaredTemplate(TName);
//       if (!relatedT)
//         return execInfo(RType.Error, `${TName} has not declared.`);

//       /** Fix Prove requirements */
//       const requirements: CallOptNode[][] = [];
//       for (let l of node.requirements) {
//         const vl: CallOptNode[] = [];
//         for (let req of l as CallOptNode[]) {
//           /**  Fix freeVars in a single requirement */
//           const fixedFreeVarsArr: string[][] = [];
//           for (let freeVars of node.freeVars) {
//             const fixedFreeVars: string[] = [];
//             for (let s of freeVars) {
//               if (s.startsWith("*")) fixedFreeVars.push(s.slice(1));
//               else fixedFreeVars.push("#" + s);
//             }
//             fixedFreeVarsArr.push(fixedFreeVars);
//           }

//           vl.push(CallOptNode.create(req.optName, fixedFreeVarsArr));
//         }

//         requirements.push(vl);
//       }

//       /** Fix template requirements */
//       const mapping = relatedT.fix(fixedVars);
//       for (let [index, opt] of node.templateNames.entries()) {
//         let name = node.templateNames[0];
//         for (let i = 1; i < index; i++) name += ":" + node.templateNames[i];
//         const curT = env.getDeclaredTemplate(name);
//         if (!curT) return execInfo(RType.Error);

//         /** new requirement */
//         for (let req of curT?.requirements as CallOptNode[]) {
//           /** get name of current requirement */
//           const fixedFreeVarsArr: string[][] = [];
//           for (let freeVars of req.optParams) {
//             const fixedFreeVars: string[] = [];
//             for (let s of freeVars) {
//               fixedFreeVars.push(mapping?.get(s) as string);
//             }
//             fixedFreeVarsArr.push(fixedFreeVars);
//           }

//           requirements[index].push(
//             CallOptNode.create(req.optName, fixedFreeVarsArr)
//           );
//         }
//       }

//       originalEnv.newStoredFact(fixedVars, relatedT, requirements);

//       return execInfo(RType.ProveTrue);
//     } else
//       return execInfo(
//         RType.ProveError,
//         "not all onlyIfs in template are satisfied."
//       );

//     function processOnlyIfCallOpt(onlyIf: CallOptNode) {
//       res = nodeExec(env, onlyIf);
//       if (onlyIf instanceof CallOptNode) {
//         for (let i = 0; i < onlyIfsThatNeedsCheck.length; i++) {
//           let checkedOpt = onlyIfsThatNeedsCheck[i] as CallOptNode;
//           let isTrue = env.isCallOptTrue(checkedOpt);

//           if (isTrue) {
//             env.newCallOptFact(checkedOpt);
//             onlyIfsThatNeedsCheck.splice(i, 1);
//             i--;
//           }
//         }
//       }
//     }

//     function handleRequirements(
//       env: LiTeXEnv,
//       optName: string,
//       params: string[][],
//       isExtraRequirement = false
//     ) {
//       const allStartWithAsterisk = params.every((subArr) =>
//         subArr.every((str) => str.startsWith("*"))
//       );
//       params = params.map((e) =>
//         e.map((s) => (s.startsWith("*") ? s.slice(1) : s))
//       );

//       if (allStartWithAsterisk) {
//         /* check requirements */
//         const res = callInferExec(env, CallOptNode.create(optName, params));
//         if (!execInfoIsTrue(res)) {
//           return execInfo(RType.Error, `${optName} is not true`);
//         }
//       } else {
//         /* emit requirements */
//         const fact = CallOptNode.create(optName, params);
//         const template = env.getDeclaredTemplate(fact);
//         if (!template) {
//           throw Error(`${optName} has not been declared.`);
//         }

//         let mapping = template.fix(fact);
//         if (!mapping) return execInfo(RType.KnowError);

//         if (isExtraRequirement) {
//           env.newStoredFact(params, template);
//         } else {
//           let noErr = template.emitRequirements(env, mapping);
//           if (!noErr) {
//             return execInfo(RType.Error, "calling undefined operator.");
//           }
//         }
//       }

//       return null; // No error
//     }
//   } catch (error) {
//     return hRunErr(env, RType.ProveError, "");
//   }
// }

function haveExec(env: LiTeXEnv, node: HaveNode): ExecInfo {
  try {
    /** If a variable is not declared, then declare it. If declared, bind new properties to it  */
    const notDeclared = node.params.filter((v) => env.declaredVars.includes(v));
    if (!notDeclared) {
      env.declareNewVar(notDeclared);
    }

    const optParamsArr = fixFree(env, node.opt, false, true);
    if (optParamsArr === undefined) return hRunErr(env, RType.HaveError);
    else {
      for (let strArrArr of optParamsArr.req) {
        env.newCallOptFact(
          CallOptNode.create(strArrArr.name, strArrArr.params)
        );
      }
    }

    return execInfo(RType.HaveTrue);
  } catch (error) {
    return hRunErr(env, RType.HaveError);
  }
}

type OptParamsType = { name: string; params: string[][] };
type FixFreeType = {
  onlyIf: OptParamsType[];
  req: OptParamsType[];
  others: OptParamsType[];
};

// Main Helper Function
//? Many executor function can be refactored using fixFree
export function fixFree(
  env: LiTeXEnv,
  opt: CallOptNode,
  fixOnlyIf: Boolean = false,
  fixReq: Boolean = false,
  relatedTemplate: TemplateNode | undefined = undefined,
  otherFrees: CallOptNode[] = []
): FixFreeType | undefined {
  if (!relatedTemplate) env.getDeclaredTemplate(opt);
  const result = {
    onlyIf: [] as OptParamsType[],
    req: [] as OptParamsType[],
    others: [] as OptParamsType[],
  };

  if (!relatedTemplate) {
    hRunErr(env, RType.Error, "exist not declared");
    return undefined;
  }

  const mapping = relatedTemplate?.fix(opt);
  if (!mapping) {
    hRunErr(env, RType.Error, "calling undeclared symbol.");
    return undefined;
  }

  if (fixReq) {
    const optParamsArr: OptParamsType[] = [];
    for (let curOpt of relatedTemplate.requirements as CallOptNode[]) {
      const fixedArrArr = _fixFreesUsingMap(mapping, curOpt.optParams);
      if (!fixedArrArr) {
        hRunErr(env, RType.Error);
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
        hRunErr(env, RType.Error);
        return undefined;
      }
      optParamsArr.push({ name: curOpt.optName, params: fixedArrArr });
    }
    result.onlyIf = optParamsArr;
  }

  if (otherFrees.length >= 1) {
    const optParamsArr: OptParamsType[] = [];
    for (let curOpt of otherFrees as CallOptNode[]) {
      const fixedArrArr = _fixFreesUsingMap(mapping, curOpt.optParams);
      if (!fixedArrArr) {
        hRunErr(env, RType.Error);
        return undefined;
      }
      optParamsArr.push({ name: curOpt.optName, params: fixedArrArr });
    }
    result.others = optParamsArr;
  }

  return result;

  function _fixFreesUsingMap(
    mapping: Map<string, string>,
    freeArrArr: string[][]
  ): string[][] | undefined {
    const fixedArrArr: string[][] = [];
    for (let freeArr of freeArrArr) {
      const arr: string[] = [];
      for (let s of freeArr) {
        const fixedS = mapping.get(s);
        if (!fixedS) arr.push(s);
        else arr.push(fixedS);
      }
      fixedArrArr.push(arr);
    }
    return fixedArrArr;
  }
}

// function callExistExec(
//   env: LiTeXEnv,
//   node: CallOptNode,
//   relatedTemplate: TemplateNode
// ): ExecInfo {
//   try {
//     /** check exist itself and emit requirements */
//     // ...

//     /** check requirements and emit exist */

//     const fixedRequirements = fixFree(
//       env,
//       node,
//       false,
//       true,
//       relatedTemplate
//     )?.req;
//     if (fixedRequirements === undefined)
//       return hRunErr(
//         env,
//         RType.Error,
//         `Invalid invocation of ${node.optName}.`
//       );

//     for (let fixedReq of fixedRequirements) {
//       const tmp = env.getDeclaredTemplate(fixedReq.name);
//       if (!tmp)
//         return hRunErr(
//           env,
//           RType.Error,
//           `${findIndex.name} has not declared.`
//         );
//       if (!env.isStoredTrueFact(fixedReq.params, tmp))
//         return execInfo(RType.Unknown);
//     }

//     env.newCallOptFact(node);

//     return execInfo(RType.True);
//   } catch (error) {
//     return hRunErr(env, RType.Error);
//   }
// }

function callDefExec(
  env: LiTeXEnv,
  node: CallOptNode,
  relatedTemplate: TemplateNode,
  calledByExist: Boolean = false
): ExecInfo {
  try {
    // check left(i.e. the opt itself)
    let leftIsTrue: Boolean = env.isStoredTrueFact(
      node.optParams,
      relatedTemplate
    );

    if (leftIsTrue) {
      const res = emitFree(env, node, relatedTemplate, false, true);
      if (!execInfoIsTrue(res)) return res;

      // const fixedRequirements = fixFree(
      //   env,
      //   node,
      //   false,
      //   true,
      //   relatedTemplate
      // )?.req;
      // if (!fixedRequirements)
      //   return hRunErr(
      //     env,
      //     RType.Error,
      //     `Invalid invocation of ${node.optName}.`
      //   );
      // // emit
      // for (let fixedReq of fixedRequirements) {
      //   const tmp = env.getDeclaredTemplate(fixedReq.name);
      //   if (!tmp)
      //     return hRunErr(
      //       env,
      //       RType.Error,
      //       `${findIndex.name} has not declared.`
      //     );
      //   env.newStoredFact(fixedReq.params, tmp);
      // }
      // return execInfo(RType.True);
    }

    let rightIsTrue = checkFree(env, node, relatedTemplate, false, true);
    // let rightIsTrue: Boolean = false;
    // const mapping = relatedTemplate.fix(node);
    // if (!mapping) return hRunErr(env, RType.Error);
    // rightIsTrue = relatedTemplate.requirementsSatisfied(env, mapping);

    if (!rightIsTrue) return execInfo(RType.Unknown);
    else {
      env.newCallOptFact(node);
    }

    if (calledByExist) (relatedTemplate as ExistNode).isTrue = true;
    return execInfo(RType.True);
  } catch (error) {
    return hRunErr(env, RType.DefError);
  }
}

export function emitFree(
  env: LiTeXEnv,
  node: CallOptNode,
  relatedTemplate: TemplateNode,
  onlyIf: Boolean,
  req: Boolean,
  otherFrees: CallOptNode[] = [] // free vars not bound to template.onlyif or req
): ExecInfo {
  const fixedFrees = fixFree(
    env,
    node,
    onlyIf,
    req,
    relatedTemplate,
    otherFrees
  );
  if (
    fixedFrees?.onlyIf === undefined ||
    fixedFrees.req === undefined ||
    fixedFrees.others === undefined
  )
    return hRunErr(env, RType.Error, `Invalid invocation of ${node.optName}.`);
  const fixWhat = fixedFrees?.onlyIf
    .concat(fixedFrees.req)
    .concat(fixedFrees.others);

  // emit
  for (let fixedReq of fixWhat) {
    const tmp = env.getDeclaredTemplate(fixedReq.name);
    if (!tmp)
      return hRunErr(env, RType.Error, `${findIndex.name} has not declared.`);
    env.newStoredFact(fixedReq.params, tmp);
  }

  return execInfo(RType.True);
}

export function checkFree(
  env: LiTeXEnv,
  node: CallOptNode,
  relatedTemplate: TemplateNode,
  onlyIf: Boolean,
  req: Boolean
): Boolean | undefined {
  const fixedFrees = fixFree(env, node, onlyIf, req, relatedTemplate);
  if (fixedFrees?.onlyIf === undefined || fixedFrees.req === undefined) {
    hRunErr(env, RType.Error, `Invalid invocation of ${node.optName}.`);
    return undefined;
  }
  const fixWhat = fixedFrees?.onlyIf.concat(fixedFrees.req);

  //
  for (let fixedReq of fixWhat) {
    const tmp = env.getDeclaredTemplate(fixedReq.name);
    if (!tmp) {
      hRunErr(env, RType.Error, `${findIndex.name} has not declared.`);
      return undefined;
    }
    const t = env.isStoredTrueFact(fixedReq.params, tmp);
    if (!t) return false;
  }

  return true;
}

function knowImpliesFactExec(env: LiTeXEnv, node: ImpliesFactNode): ExecInfo {
  try {
    const tmp = env.getDeclaredTemplate(node.callOpt);
    if (!tmp) {
      hRunErr(env, RType.Error, `${findIndex.name} has not declared.`);
      return execInfo(RType.KnowError);
    }

    env.newStoredFact(
      node.callOpt.optParams,
      tmp,
      node.requirements,
      node.onlyIfExprs
    );

    return execInfo(RType.KnowTrue);
  } catch (error) {
    return hRunErr(env, RType.KnowError);
  }
}

function proveExec(env: LiTeXEnv, node: YAProveNode): ExecInfo {
  try {
    const relatedT = env.getDeclaredTemplate(node.templateNames.join(":"));
    switch (relatedT?.type) {
      case LiTeXNodeType.DefNode:
        return proveDefExec(env, node, relatedT);
    }
    return hRunErr(env, RType.ProveError);
  } catch (error) {
    return hRunErr(env, RType.ProveError);
  }
}

function proveDefExec(
  env: LiTeXEnv,
  node: YAProveNode,
  relatedT: TemplateNode
): ExecInfo {
  try {
    const onlyIfs = node.onlyIfExprs as CallOptNode[];
    const req: CallOptNode[] = (node.requirements as CallOptNode[][]).flat();
    const relOpt = CallOptNode.create(node.templateNames.join(":"), node.vars);
    const newEnv = new LiTeXEnv();
    newEnv.father = env;

    const TFixFree = fixFree(env, relOpt, true, true, relatedT);
    if (!TFixFree) return hRunErr(env, RType.ProveError);

    const reqFixFree = fixFree(env, relOpt, false, false, relatedT, onlyIfs);
    if (!reqFixFree) return hRunErr(env, RType.ProveError);

    const onlyIfFixFree = fixFree(env, relOpt, false, false, relatedT, req);
    if (!onlyIfFixFree) return hRunErr(env, RType.ProveError);

    const mapping = relatedT.fix(relOpt);
    if (!mapping) {
      return hRunErr(env, RType.Error, "calling undeclared symbol.");
    }

    /**Execute onlyIfs in the prove block*/
    for (let ) {

    }

    /**After */
    
  } catch (error) {}
}
