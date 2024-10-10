import { findIndex } from "lodash";
import {
  CallOptNode,
  CallOptsNode,
  KnowNode,
  L_Node,
  L_NodeType,
  LetNode,
  CanBeKnownNode,
  TNode,
  YAProveNode,
  HaveNode,
  ExistNode,
  ImpliesFactNode,
} from "./ast";
import { L_BuiltinKeywords } from "./builtins";
import { L_Keywords } from "./common";
import { L_Env } from "./env";

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
  ProveFailed,
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
  [RType.ProveFailed]: "prove: failed",
  [RType.KnowEverythingError]: "know_everything: error",
  [RType.KnowEverythingTrue]: "know_everything: true",
  [RType.ExistError]: "exist: error",
  [RType.ExistTrue]: "exist: true",
};

export function RInfoIsTrue(res: RInfo) {
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

export function hRunErr(env: L_Env, type: RType, message: string = ""): RInfo {
  env.pushNewError(RTypeMap[type] + ": " + message);
  return hInfo(type, message);
}

export const hInfo = (t: RType, s: string = "") => {
  return { type: t, message: s };
};
export type RInfo = { type: RType; message: string };
export const ErrorRInfo = { type: RType.Error, message: "" };

export function nodeExec(env: L_Env, node: L_Node): RInfo {
  try {
    switch (node.type) {
      case L_NodeType.DefNode:
      case L_NodeType.InferNode:
      case L_NodeType.ExistNode:
        return templateDeclExec(env, node as TNode);
      case L_NodeType.KnowNode:
        return yaKnowExec(env, node as KnowNode);
      case L_NodeType.CallOptsNode:
        return callOptsExec(env, node as CallOptsNode);
      case L_NodeType.LetNode:
        return letExec(env, node as LetNode);
      case L_NodeType.ProofNode:
        // return hInfo(RType.True);
        return proveExec(env, node as YAProveNode);
      case L_NodeType.HaveNode:
        return haveExec(env, node as HaveNode);
    }
    return hInfo(RType.Error, "Stmt");
  } catch (error) {
    return hRunErr(env, RType.Error, "Stmt");
  }
}

function letExec(env: L_Env, node: LetNode): RInfo {
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
      if (!RInfoIsTrue(info)) return hRunErr(env, RType.LetError, info.message);
    }

    return hInfo(RType.LetTrue);
  } catch (error) {
    return hRunErr(env, RType.LetError, "let");
  }
}

function callOptsExec(env: L_Env, node: CallOptsNode): RInfo {
  try {
    const whatIsTrue: string[] = [];
    for (const fact of (node as CallOptsNode).nodes) {
      const relatedTemplate = env.getRelT(fact as CallOptNode);
      if (!relatedTemplate)
        return hRunErr(env, RType.Error, `${fact.optName} is not declared.`);
      let info: RInfo = ErrorRInfo;
      switch (relatedTemplate.type) {
        case L_NodeType.ExistNode:
          info = callDefExec(env, fact, relatedTemplate, true);
          break;
        case L_NodeType.DefNode:
          info = callDefExec(env, fact, relatedTemplate);
          break;
        case L_NodeType.InferNode:
          info = callInferExec(env, fact, relatedTemplate);
          break;
      }
      if (info.type === RType.Unknown || info.type === RType.False) {
        return info;
      }
      if (!RInfoIsTrue(info)) return hRunErr(env, RType.Error, "");
      whatIsTrue.push(`${fact.optName} ${fact.optParams}`);
    }
    return hInfo(RType.True, whatIsTrue.join(";"));
  } catch (error) {
    return hRunErr(env, RType.Error, "call operators");
  }
}

function callInferExec(
  env: L_Env,
  node: CallOptNode,
  relatedTemplate: TNode | undefined = undefined
): RInfo {
  try {
    const builtinFunc = L_BuiltinKeywords[node.optName];
    if (builtinFunc) {
      return builtinFunc(env, node);
    }

    if (!relatedTemplate) relatedTemplate = env.getRelT(node);

    if (!relatedTemplate)
      return hRunErr(env, RType.False, node.optName + " is not declared.");

    // if (relatedTemplate?.type === L_NodeType.ExistNode) {
    //   return callExistExec(env, node as CallOptNode);
    // } else if (relatedTemplate.type === L_NodeType.DefNode) {
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

    return hInfo(
      RType.DefTrue,
      `${node.optName} itself and its requirements are all satisfied.`
    );
  } catch (error) {
    return hRunErr(env, RType.Error, "call operator");
  }
}

function templateDeclExec(env: L_Env, node: TNode): RInfo {
  try {
    const declaredTemplates = env.declaredTemplates as Map<string, TNode>;

    // Check if the template name already exists
    if (!node.isRedefine && declaredTemplates.has(node.declOptName)) {
      throw new Error(
        `Template '${node.declOptName}' has already been declared. Duplicate declarations are not allowed.`
      );
    }

    if (L_Keywords.includes(node.declOptName)) {
      throw new Error(`Template '${node.declOptName}' is L_ keyword.`);
    }

    // If not already declared, set the new template
    declaredTemplates.set(node.declOptName, node);

    // move templates(pure, questionMark) from node.onlyIfs to node.declaredTemplates
    let res = node.initDeclaredTemplates(env);
    if (!RInfoIsTrue(res)) return hRunErr(env, RType.DefError);

    switch (node.type) {
      case L_NodeType.DefNode:
        return hInfo(RType.DefTrue, "def");
      case L_NodeType.ExistNode:
        return hInfo(RType.DefTrue, "exist");
      case L_NodeType.InferNode:
        return hInfo(RType.DefTrue, "infer");
    }

    return hInfo(RType.Error);
  } catch (error) {
    return hRunErr(
      env,
      RType.DefError,
      `Template declaration error: ${(error as Error).message}`
    );
  }
}

function yaKnowExec(env: L_Env, node: KnowNode): RInfo {
  try {
    let facts: CanBeKnownNode[] = [];
    let isKnowEverything: Boolean = false;
    let res: RInfo = { type: RType.Error, message: "" };

    if (node.type === L_NodeType.KnowNode) {
      facts = (node as KnowNode).facts;
      isKnowEverything = (node as KnowNode).isKnowEverything;
    }

    for (const fact of facts) {
      switch (fact.type) {
        case L_NodeType.CallOptNode:
          if (isKnowEverything)
            res = yaKnowEverythingCallOptExec(env, fact as CallOptNode);
          else res = yaKnowCallOptExec(env, fact as CallOptNode);
          break;
        case L_NodeType.ImpliesFactNode:
          res = knowImpliesFactExec(env, fact as ImpliesFactNode);
          break;
        case L_NodeType.DefNode:
        case L_NodeType.InferNode: {
          res = templateDeclExec(env, fact as TNode);
          if (isKnowEverything) {
            res = yaKnowEverythingCallOptExec(
              env,
              CallOptNode.create((fact as TNode).declOptName, [
                (fact as TNode).freeVars,
              ])
            );
          } else {
            res = yaKnowCallOptExec(
              env,
              CallOptNode.create((fact as TNode).declOptName, [
                (fact as TNode).freeVars,
              ])
            );
          }
          break;
        }
      }
      if (!RInfoIsTrue(res)) return res;
    }

    return hInfo(RType.KnowTrue);
  } catch (error) {
    return hRunErr(env, RType.KnowError, "know");
  }
}

function yaKnowEverythingCallOptExec(env: L_Env, fact: CallOptNode): RInfo {
  try {
    let res: RInfo = { type: RType.Error, message: "" };
    res = yaKnowCallOptExec(env, fact);

    const template = env.getRelT(fact as CallOptNode);
    if (!template)
      throw Error(`${(fact as CallOptNode).optName} has not been declared.`);

    emitFree(env, fact, template, true, true);

    // let mapping = template.fix(fact);
    // if (!mapping) return hInfo(RType.KnowError);

    // template.emitOnlyIfs(env, mapping);
    // let noErr = template.emitRequirements(env, mapping);
    // if (!noErr)
    //   return hInfo(RType.Error, "calling undefined operator.");

    // if (!RInfoIsTrue(res)) return res;

    return hInfo(RType.KnowTrue);
  } catch (error) {
    return hRunErr(env, RType.KnowEverythingError, "");
  }
}

function yaKnowCallOptExec(env: L_Env, node: CallOptNode): RInfo {
  try {
    if (
      !node.optParams.every((ls) =>
        ls.every((s) => env.declaredVars.includes(s) || s.startsWith("#"))
      )
    ) {
      return hRunErr(env, RType.KnowError, "symbol not declared.");
    }

    let relatedTemplate = env.getRelT(node);

    if (!relatedTemplate)
      return hInfo(RType.KnowUndeclared, node.optName + " has not declared");

    //! THE CLASSICAL WAY OF TRANSFORMING FREE VAR INTO FIXED AND EMIT
    env.newStoredFact(
      node.optParams,
      env.getRelT(node) as TNode,
      node.requirements
    );

    /** The following lines should be refactored */
    // let rightIsTrue: Boolean = false;
    // const mapping = relatedTemplate.fix(node);
    // if (!mapping) return hRunErr(env, RType.Error);
    // rightIsTrue = relatedTemplate.requirementsSatisfied(env, mapping);

    let rightIsTrue = checkFree(env, node, relatedTemplate, false, true);

    if (!rightIsTrue) return hInfo(RType.Unknown);
    else {
      const res = emitFree(env, node, relatedTemplate, true, false);
      if (!RInfoIsTrue(res)) return res;

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
      //   const tmp = env.getRelT(fixedReq.name);
      //   if (!tmp)
      //     return hRunErr(
      //       env,
      //       RType.Error,
      //       `${findIndex.name} has not declared.`
      //     );
      //   env.newStoredFact(fixedReq.params, tmp);
      // }
    }

    return hInfo(RType.KnowTrue);
    // else return hInfo(RType.KnowError, res.message);
  } catch (error) {
    return hRunErr(env, RType.KnowError, "");
  }
}

// function proveInferExec(env: L_Env, node: YAProveNode): RInfo {
//   try {
//     const relatedTemplate = env.getRelT(
//       node.templateNames.join(":")
//     );
//     if (!relatedTemplate)
//       return hInfo(
//         RType.ProveError,
//         `${node.templateNames.join(":")} is not declared.`
//       );
//     const originalEnv = env;
//     env = new L_Env(env);

//     // introduce vars into new env
//     for (let l of node.freeVars) {
//       for (let freeVar of l) {
//         if (freeVar.startsWith("*")) continue;
//         else if (freeVar.startsWith("#")) {
//           return hInfo(
//             RType.ProveError,
//             "parameters in requirement should not start with #"
//           );
//         } else {
//           let res = env.newVar(freeVar);
//           if (!res)
//             return hInfo(
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

//     let res: RInfo = RInfo(RType.ProveError);
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
//       const relatedT = env.getRelT(TName);
//       if (!relatedT)
//         return hInfo(RType.Error, `${TName} has not declared.`);

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
//         const curT = env.getRelT(name);
//         if (!curT) return hInfo(RType.Error);

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

//       return hInfo(RType.ProveTrue);
//     } else
//       return hInfo(
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
//       env: L_Env,
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
//         if (!RInfoIsTrue(res)) {
//           return hInfo(RType.Error, `${optName} is not true`);
//         }
//       } else {
//         /* emit requirements */
//         const fact = CallOptNode.create(optName, params);
//         const template = env.getRelT(fact);
//         if (!template) {
//           throw Error(`${optName} has not been declared.`);
//         }

//         let mapping = template.fix(fact);
//         if (!mapping) return hInfo(RType.KnowError);

//         if (isExtraRequirement) {
//           env.newStoredFact(params, template);
//         } else {
//           let noErr = template.emitRequirements(env, mapping);
//           if (!noErr) {
//             return hInfo(RType.Error, "calling undefined operator.");
//           }
//         }
//       }

//       return null; // No error
//     }
//   } catch (error) {
//     return hRunErr(env, RType.ProveError, "");
//   }
// }

function haveExec(env: L_Env, node: HaveNode): RInfo {
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

    return hInfo(RType.HaveTrue);
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
  env: L_Env,
  opt: CallOptNode,
  fixOnlyIf: Boolean = false,
  fixReq: Boolean = false,
  relatedTemplate: TNode | undefined = undefined,
  otherFrees: CallOptNode[] = []
): FixFreeType | undefined {
  if (!relatedTemplate) env.getRelT(opt);
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
//   env: L_Env,
//   node: CallOptNode,
//   relatedTemplate: TNode
// ): RInfo {
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
//       const tmp = env.getRelT(fixedReq.name);
//       if (!tmp)
//         return hRunErr(
//           env,
//           RType.Error,
//           `${findIndex.name} has not declared.`
//         );
//       if (!env.isStoredTrueFact(fixedReq.params, tmp))
//         return hInfo(RType.Unknown);
//     }

//     env.newCallOptFact(node);

//     return hInfo(RType.True);
//   } catch (error) {
//     return hRunErr(env, RType.Error);
//   }
// }

function callDefExec(
  env: L_Env,
  node: CallOptNode,
  relatedTemplate: TNode,
  calledByExist: Boolean = false
): RInfo {
  try {
    // check left(i.e. the opt itself)
    let leftIsTrue: Boolean = env.isStoredTrueFact(
      node.optParams,
      relatedTemplate
    );

    if (leftIsTrue) {
      const res = emitFree(env, node, relatedTemplate, false, true);
      if (!RInfoIsTrue(res)) return res;

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
      //   const tmp = env.getRelT(fixedReq.name);
      //   if (!tmp)
      //     return hRunErr(
      //       env,
      //       RType.Error,
      //       `${findIndex.name} has not declared.`
      //     );
      //   env.newStoredFact(fixedReq.params, tmp);
      // }
      // return hInfo(RType.True);
    }

    let rightIsTrue = checkFree(env, node, relatedTemplate, false, true);
    // let rightIsTrue: Boolean = false;
    // const mapping = relatedTemplate.fix(node);
    // if (!mapping) return hRunErr(env, RType.Error);
    // rightIsTrue = relatedTemplate.requirementsSatisfied(env, mapping);

    if (!rightIsTrue) return hInfo(RType.Unknown);
    else {
      env.newCallOptFact(node);
    }

    if (calledByExist) (relatedTemplate as ExistNode).isTrue = true;
    return hInfo(RType.True);
  } catch (error) {
    return hRunErr(env, RType.DefError);
  }
}

export function emitFree(
  env: L_Env,
  node: CallOptNode,
  relatedTemplate: TNode,
  onlyIf: Boolean,
  req: Boolean,
  otherFrees: CallOptNode[] = [] // free vars not bound to template.onlyif or req
): RInfo {
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
    const tmp = env.getRelT(fixedReq.name);
    if (!tmp)
      return hRunErr(env, RType.Error, `${findIndex.name} has not declared.`);
    env.newStoredFact(fixedReq.params, tmp);
  }

  return hInfo(RType.True);
}

export function checkFree(
  env: L_Env,
  node: CallOptNode,
  relatedTemplate: TNode,
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
    const tmp = env.getRelT(fixedReq.name);
    if (!tmp) {
      hRunErr(env, RType.Error, `${findIndex.name} has not declared.`);
      return undefined;
    }
    const t = env.isStoredTrueFact(fixedReq.params, tmp);
    if (!t) return false;
  }

  return true;
}

function knowImpliesFactExec(env: L_Env, node: ImpliesFactNode): RInfo {
  try {
    const tmp = env.getRelT(node.callOpt);
    if (!tmp) {
      hRunErr(env, RType.Error, `${findIndex.name} has not declared.`);
      return hInfo(RType.KnowError);
    }

    env.newStoredFact(
      node.callOpt.optParams,
      tmp,
      node.requirements,
      node.onlyIfExprs
    );

    return hInfo(RType.KnowTrue);
  } catch (error) {
    return hRunErr(env, RType.KnowError);
  }
}

function proveExec(env: L_Env, node: YAProveNode): RInfo {
  try {
    const relatedT = env.getRelT(node.templateNames.join(":"));
    switch (relatedT?.type) {
      case L_NodeType.InferNode:
        return proveInferExec(env, node, relatedT);
      case L_NodeType.DefNode:
        return proveDefExec(env, node, relatedT);
    }
    return hRunErr(env, RType.ProveError);
  } catch (error) {
    return hRunErr(env, RType.ProveError);
  }
}

function proveDefExec(env: L_Env, node: YAProveNode, relatedT: TNode): RInfo {
  try {
    const onlyIfs = node.onlyIfExprs as L_Node[];
    const req: CallOptNode[] = (node.requirements as CallOptNode[][]).flat();
    const newEnv = new L_Env();
    newEnv.father = env;
    env = newEnv;

    const relOpt = CallOptNode.create(
      node.templateNames.join(":"),
      node.vars.map((ls) => ls.map((s) => (s.startsWith("*") ? s.slice(1) : s)))
    );
    const TFixFree = fixFree(env, relOpt, true, true, relatedT);
    if (!TFixFree) return hRunErr(env, RType.ProveError);

    /**Declare variables in newEnv */
    for (let varToDecl of node.vars.flat()) {
      if (varToDecl.startsWith("*") || newEnv.declaredVars.includes(varToDecl))
        continue;
      newEnv.declareNewVar(varToDecl);
    }

    /**Execute onlyIfs in the prove block*/
    for (const [i, curNode] of onlyIfs.entries()) {
      const res = nodeExec(newEnv, curNode);
      if (!RInfoIsTrue(res))
        return hInfo(RType.ProveFailed, `${i}th stmt failed.`);
    }

    /**After execution, check whether template requirements are satisfied.*/
    for (const [i, fact] of TFixFree.onlyIf.entries()) {
      const tmp = env.getRelT(fact.name);
      if (!tmp)
        return hRunErr(env, RType.ProveError, `${fact.name} not declared`);
      const isT = env.isStoredTrueFact(fact.params, tmp);
      if (!isT) return hInfo(RType.ProveFailed, `${fact.name} not satisfied.`);
    }

    return hInfo(RType.ProveTrue);
  } catch (error) {
    return hRunErr(env, RType.ProveError);
  }
}

function proveInferExec(env: L_Env, node: YAProveNode, relatedT: TNode): RInfo {
  try {
    const onlyIfs = node.onlyIfExprs as L_Node[];
    const req: CallOptNode[] = (node.requirements as CallOptNode[][]).flat();
    const newEnv = new L_Env();
    newEnv.father = env;
    env = newEnv;

    const relOpt = CallOptNode.create(
      node.templateNames.join(":"),
      node.vars.map((ls) => ls.map((s) => (s.startsWith("*") ? s.slice(1) : s)))
    );
    const TFixFree = fixFree(env, relOpt, true, true, relatedT);
    if (!TFixFree) return hRunErr(env, RType.ProveError);

    /**Declare variables in newEnv */
    for (let varToDecl of node.vars.flat()) {
      if (varToDecl.startsWith("*") || newEnv.declaredVars.includes(varToDecl))
        continue;
      newEnv.declareNewVar(varToDecl);
    }

    /**Emit req in newEnv */
    for (const [i, fact] of req.entries()) {
      const tmp = env.getRelT(fact.optName);
      if (!tmp)
        return hRunErr(env, RType.ProveError, `${fact.optName} not declared`);
      newEnv.newStoredFact(fact.optParams, tmp, [], []);
    }

    /**Execute onlyIfs in the prove block*/
    for (const [i, curNode] of onlyIfs.entries()) {
      const res = nodeExec(newEnv, curNode);
      if (!RInfoIsTrue(res))
        return hInfo(RType.ProveFailed, `${i}th stmt failed.`);
    }

    /**After execution, check whether template requirements are satisfied.*/
    for (const [i, fact] of TFixFree.onlyIf.entries()) {
      const tmp = env.getRelT(fact.name);
      if (!tmp)
        return hRunErr(env, RType.ProveError, `${fact.name} not declared`);
      const isT = env.isStoredTrueFact(fact.params, tmp);
      if (!isT) return hInfo(RType.ProveFailed, `${fact.name} not satisfied.`);
    }

    return hInfo(RType.ProveTrue);
  } catch (error) {
    return hRunErr(env, RType.ProveError);
  }
}
