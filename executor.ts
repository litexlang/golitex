import { isNull } from "lodash";
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
} from "./ast";
import { L_Keywords } from "./common";
import { L_Env } from "./env";
import { fixOpt, isL_OutErr } from "./shared";

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
  HaveFailed,
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
  [RType.HaveFailed]: "have: failed",
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

function RInfoIsError(res: RInfo) {
  function isErrorRType(type: RType): boolean {
    const typeName = RType[type]; // 获取枚举的键名
    return typeName.endsWith("Error");
  }

  return isErrorRType(res.type);
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
export const hNoRelTErr = (
  opt: CallOptNode | string,
  type: RType = RType.Error
) => {
  if (opt instanceof CallOptNode)
    return hInfo(type, opt.optName + " not declared.");
  else return hInfo(type, opt + " not declared.");
};
export const hFixFreeErr = (
  opt: CallOptNode | string,
  type: RType = RType.Error
) => {
  if (opt instanceof CallOptNode)
    return hInfo(type, `fail to instantiate ${opt.optName}`);
  else return hInfo(type, `fail to instantiate ${opt}`);
};

export function nodeExec(env: L_Env, node: L_Node): RInfo {
  try {
    switch (node.type) {
      case L_NodeType.DefNode:
      case L_NodeType.InferNode:
      case L_NodeType.ExistNode:
        return templateDeclExec(env, node as TNode);
      case L_NodeType.KnowNode:
        return knowExec(env, node as KnowNode);
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

function callOptExec(env: L_Env, fact: CallOptNode): RInfo {
  const relT = env.getRelT(fact as CallOptNode);
  if (!relT)
    return hRunErr(env, RType.Error, `${fact.optName} is not declared.`);
  let info: RInfo = ErrorRInfo;
  switch (relT.type) {
    case L_NodeType.ExistNode:
      info = callExistExec(env, fact, relT);
      break;
    case L_NodeType.DefNode:
      info = callDefExec(env, fact, relT);
      break;
    case L_NodeType.InferNode:
      info = callInferExec(env, fact, relT);
      break;
  }
  if (info.type === RType.Unknown || info.type === RType.False) {
    return info;
  }
  if (!RInfoIsTrue(info)) return hRunErr(env, RType.Error, "");
  return hInfo(RType.True);
}

function callOptsExec(env: L_Env, node: CallOptsNode): RInfo {
  try {
    const whatIsTrue: string[] = [];
    for (const fact of (node as CallOptsNode).nodes) {
      const info = callOptExec(env, fact);
      if (info.type === RType.Unknown || info.type === RType.False) {
        return hInfo(info.type);
      } else if (!RInfoIsTrue(info)) {
        return hRunErr(env, info.type);
      }
    }
    return hInfo(RType.True, whatIsTrue.join(";"));
  } catch (error) {
    return hRunErr(env, RType.Error, "call operators");
  }
}

function callInferExec(
  env: L_Env,
  node: CallOptNode,
  relT: TNode | undefined = undefined
): RInfo {
  try {
    // const builtinFunc = L_Builtins[node.optName];
    // if (builtinFunc) {
    //   return builtinFunc(env, node);
    // }

    // if (!relT) relT = env.getRelT(node);
    // if (!relT) return hNoRelTErr(node, RType.Error);

    // // check itself
    // let isT: Boolean | undefined = env.isStoredTrueFact(node.optParams, relT);
    // if (!isT) return hInfo(RType.Unknown, `${node.optName} itself unsatisfied`);

    // // check all requirements
    // isT = checkFree(env, node, relT, false, true);

    // if (isT === undefined)
    //   return hRunErr(env, RType.Error, "check infer requirement error.");
    // if (isT === false)
    //   return hInfo(RType.Unknown, `${node.optName} requirements unsatisfied.`);

    // // emit
    // emitFree(env, node, relT, true, false);

    return hInfo(RType.True);
  } catch (error) {
    return hRunErr(env, RType.Error, `call ${node.optName}`);
  }
}

function templateDeclExec(env: L_Env, node: TNode): RInfo {
  try {
    // Check if the template name already exists
    if (!node.isRedefine && env.declaredTemplates.has(node.name)) {
      return hRunErr(env, RType.DefError, `${node.name} has declared`);
    }

    if (L_Keywords.includes(node.name)) {
      return hRunErr(env, RType.DefError, `'${node.name}' is keyword.`);
    }

    // If not already declared, set the new template
    env.declaredTemplates.set(node.name, node);

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
    return hRunErr(env, RType.DefError);
  }
}

function knowExec(env: L_Env, node: KnowNode): RInfo {
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
        // case L_NodeType.ImpliesFactNode:
        //   res = knowImpliesFactExec(env, fact as ImpliesFactNode);
        //   break;
        case L_NodeType.DefNode:
        case L_NodeType.InferNode: {
          res = templateDeclExec(env, fact as TNode);
          if (isKnowEverything) {
            res = yaKnowEverythingCallOptExec(
              env,
              CallOptNode.create((fact as TNode).name, [
                (fact as TNode).freeVars,
              ])
            );
          } else {
            res = yaKnowCallOptExec(
              env,
              CallOptNode.create((fact as TNode).name, [
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
    // let res: RInfo = { type: RType.Error, message: "" };
    // res = yaKnowCallOptExec(env, fact);

    // const template = env.getRelT(fact as CallOptNode);
    // if (!template)
    //   throw Error(`${(fact as CallOptNode).optName} has not been declared.`);

    // emitFree(env, fact, template, true, true);

    return hInfo(RType.KnowTrue);
  } catch (error) {
    return hRunErr(env, RType.KnowEverythingError, "");
  }
}

function yaKnowCallOptExec(env: L_Env, node: CallOptNode): RInfo {
  try {
    if (!env.getRelT(node)) return hInfo(RType.KnowError);

    if (
      !node.optParams.every((ls) =>
        ls.every((s) => env.declaredVars.includes(s) || s.startsWith("#"))
      )
    )
      return hRunErr(env, RType.KnowError, "symbol not declared.");

    if (node.optParams.every((ls) => ls.every((s) => s[0] !== "#")))
      // If every var in callOpt is not 'forall', we emit onlyIf immediately
      env.YANewFactEmit(node);
    else env.YANewFactEmit(node, false);

    // env.YANewFactEmit()
    return hInfo(RType.KnowTrue);
  } catch (error) {
    return hRunErr(env, RType.KnowError);
  }
}

// function yaKnowCallOptExec(env: L_Env, node: CallOptNode): RInfo {
//   try {
//     if (
//       !node.optParams.every((ls) =>
//         ls.every((s) => env.declaredVars.includes(s) || s.startsWith("#"))
//       )
//     ) {
//       return hRunErr(env, RType.KnowError, "symbol not declared.");
//     }

//     let relT = env.getRelT(node);

//     if (!relT)
//       return hInfo(RType.KnowUndeclared, node.optName + " has not declared");

//     /**Know Exist Opt */
//     if (relT.type === L_NodeType.ExistNode) {
//       (relT as ExistNode).isTrue = true;
//       return hInfo(RType.KnowTrue);
//     }

//     //! THE CLASSICAL WAY OF TRANSFORMING FREE VAR INTO FIXED AND EMIT
//     env.newStoredFact(node.optParams, env.getRelT(node) as TNode, node.req);

//     let rightIsTrue = checkFree(env, node, relT, false, true);

//     if (!rightIsTrue) return hInfo(RType.Unknown);
//     else {
//       const res = emitFree(env, node, relT, true, false);
//       if (!RInfoIsTrue(res)) return res;
//     }

//     return hInfo(RType.KnowTrue);
//   } catch (error) {
//     return hRunErr(env, RType.KnowError, "");
//   }
// }

function haveExec(env: L_Env, node: HaveNode): RInfo {
  try {
    // const relT = env.getRelT(node.opt);
    // if (!relT) return hNoRelTErr(node.opt, RType.HaveError);
    // const req = fixFree(env, node.opt, false, true, relT)?.req;
    // if (!req) return hFixFreeErr(node.opt, RType.HaveError);
    // for (const optParams of req) {
    //   if (!env.isFact(optParams.name, optParams.params))
    //     return hInfo(RType.HaveFailed);
    // }

    // (relT as ExistNode).isTrue = true;
    return hInfo(RType.HaveTrue);
  } catch (error) {
    return hRunErr(env, RType.HaveError);
  }
}

export type OptParamsType = { name: string; params: string[][] };
export type FixFreeType = {
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
  relT: TNode | undefined = undefined,
  otherFrees: CallOptNode[] = []
): FixFreeType | undefined {
  if (!relT) env.getRelT(opt);
  const result = {
    onlyIf: [] as OptParamsType[],
    req: [] as OptParamsType[],
    others: [] as OptParamsType[],
  };

  if (!relT) {
    hRunErr(env, RType.Error, "exist not declared");
    return undefined;
  }

  const mapping = relT?.fix(opt);
  if (!mapping) {
    hRunErr(env, RType.Error, "calling undeclared symbol.");
    return undefined;
  }

  if (fixReq) {
    const optParamsArr: OptParamsType[] = [];
    for (let curOpt of relT.requirements as CallOptNode[]) {
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
    for (let curOpt of relT.onlyIfExprs as CallOptNode[]) {
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

// function callDefExec(
//   env: L_Env,
//   node: CallOptNode,
//   relT: TNode,
//   calledByExist: Boolean = false
// ): RInfo {
//   try {
//     // check left(i.e. the opt itself)
//     let leftIsTrue: Boolean = env.isStoredTrueFact(node.optParams, relT);

//     if (leftIsTrue) {
//       const res = emitFree(env, node, relT, false, true);
//       if (!RInfoIsTrue(res)) return res;
//     }

//     let rightIsTrue = checkFree(env, node, relT, false, true);

//     if (!rightIsTrue) return hInfo(RType.Unknown);
//     else {
//       env.newCallOptFact(node);
//     }

//     if (calledByExist) (relT as ExistNode).isTrue = true;
//     return hInfo(RType.True);
//   } catch (error) {
//     return hRunErr(env, RType.DefError);
//   }
// }

function callExistExec(env: L_Env, node: CallOptNode, relT: TNode): RInfo {
  try {
    return hInfo(RType.ExistTrue);
  } catch (error) {
    return hRunErr(env, RType.ExistError);
  }
}

function callDefExec(
  env: L_Env,
  node: CallOptNode,
  relT: TNode
  // calledByExist: Boolean = false
): RInfo {
  try {
    //TODO:  There are two trues of callDef: 1. itself 2. all requirements satisfied.

    const res = env.yaDefCheckEmit(node);
    if (isL_OutErr(res)) return hRunErr(env, RType.DefError, res.err);

    if (res.v) {
      node.onlyIFs.forEach((e) => env.YANewFactEmit(e, false));
      return hInfo(RType.True);
    }

    let temp = fixOpt(
      env,
      node,
      relT.getSelfFathersFreeVars(),
      relT.getSelfFathersReq()
    );
    if (isL_OutErr(temp)) return hRunErr(env, RType.Error);
    const fixedReq = temp.v as CallOptNode[];

    let isT = false;
    if (fixedReq.length > 0) {
      isT = true;
      for (const req of fixedReq) {
        const res = callOptExec(env, req);
        if (res.type !== RType.True) {
          isT = false;
          break;
        }
      }
    }

    return isT ? hInfo(RType.True) : hInfo(RType.Unknown);
  } catch (error) {
    return hRunErr(env, RType.DefError);
  }
}

// export function emitFree(
//   env: L_Env,
//   node: CallOptNode,
//   relT: TNode,
//   onlyIf: Boolean,
//   req: Boolean,
//   otherFrees: CallOptNode[] = [] // free vars not bound to template.onlyif or req
// ): RInfo {
//   const fixedFrees = fixFree(env, node, onlyIf, req, relT, otherFrees);
//   if (
//     fixedFrees?.onlyIf === undefined ||
//     fixedFrees.req === undefined ||
//     fixedFrees.others === undefined
//   )
//     return hRunErr(env, RType.Error, `Invalid invocation of ${node.optName}.`);
//   const fixWhat = fixedFrees?.onlyIf
//     .concat(fixedFrees.req)
//     .concat(fixedFrees.others);

//   // emit
//   for (let fixedReq of fixWhat) {
//     const tmp = env.getRelT(fixedReq.name);
//     if (!tmp)
//       return hRunErr(env, RType.Error, `${findIndex.name} has not declared.`);
//     env.newStoredFact(fixedReq.params, tmp);
//   }

//   return hInfo(RType.True);
// }

// export function checkFree(
//   env: L_Env,
//   node: CallOptNode,
//   relT: TNode,
//   onlyIf: Boolean,
//   req: Boolean
// ): Boolean | undefined {
//   const fixedFrees = fixFree(env, node, onlyIf, req, relT);
//   if (fixedFrees?.onlyIf === undefined || fixedFrees.req === undefined) {
//     hRunErr(env, RType.Error, `Invalid invocation of ${node.optName}.`);
//     return undefined;
//   }
//   const fixWhat = fixedFrees?.onlyIf.concat(fixedFrees.req);

//   //
//   for (let fixedReq of fixWhat) {
//     const tmp = env.getRelT(fixedReq.name);
//     if (!tmp) {
//       hRunErr(env, RType.Error, `${findIndex.name} has not declared.`);
//       return undefined;
//     }
//     const t = env.isStoredTrueFact(fixedReq.params, tmp);
//     if (!t) return false;
//   }

//   return true;
// }

// function knowImpliesFactExec(env: L_Env, node: ImpliesFactNode): RInfo {
//   try {
//     const tmp = env.getRelT(node.callOpt);
//     if (!tmp) {
//       hRunErr(env, RType.Error, `${findIndex.name} has not declared.`);
//       return hInfo(RType.KnowError);
//     }

//     env.newStoredFact(
//       node.callOpt.optParams,
//       tmp,
//       node.requirements,
//       node.onlyIfExprs
//     );

//     return hInfo(RType.KnowTrue);
//   } catch (error) {
//     return hRunErr(env, RType.KnowError);
//   }
// }

function proveExec(env: L_Env, node: YAProveNode): RInfo {
  try {
    const relatedT = env.getRelT(node.opt.optName);
    switch (relatedT?.type) {
      case L_NodeType.InferNode:
        return proveInferExec(env, node, relatedT);
      case L_NodeType.DefNode:
        return proveDefExec(env, node, relatedT);
    }

    return hRunErr(
      env,
      RType.ProveError,
      `prove keyword should be followed by declared template name`
    );
  } catch (error) {
    return hRunErr(env, RType.ProveError);
  }
}

function proveDefExec(env: L_Env, node: YAProveNode, relatedT: TNode): RInfo {
  try {
    // /** The only different between proveDef and proveInfer is: case def template requirements are used to check; in case infer they are used as pre-conditions*/
    // const onlyIfs = node.onlyIfExprs as L_Node[];
    // const req: CallOptNode[] = node.opt.req;
    // const newEnv = new L_Env();
    // newEnv.father = env;
    // env = newEnv;

    // const relOpt = CallOptNode.create(
    //   node.opt.optName,
    //   node.opt.optParams.map((ls) =>
    //     ls.map((s) => (s.startsWith("*") ? s.slice(1) : s))
    //   )
    // );
    // const TFixFree = fixFree(env, relOpt, true, true, relatedT);
    // if (!TFixFree) return hRunErr(env, RType.ProveError);

    // /**Declare variables in newEnv */
    // for (let varToDecl of node.opt.optParams.flat()) {
    //   if (varToDecl.startsWith("*") || newEnv.declaredVars.includes(varToDecl))
    //     continue;
    //   newEnv.declareNewVar(varToDecl);
    // }

    // /**Execute onlyIfs in the prove block*/
    // for (const [i, curNode] of onlyIfs.entries()) {
    //   const res = nodeExec(newEnv, curNode);
    //   if (!RInfoIsTrue(res))
    //     return hInfo(RType.ProveFailed, `${i}th stmt failed.`);
    // }

    // /**After execution, check whether template requirements are satisfied.*/
    // for (const [i, fact] of TFixFree.req.entries()) {
    //   const tmp = env.getRelT(fact.name);
    //   if (!tmp)
    //     return hRunErr(env, RType.ProveError, `${fact.name} not declared`);
    //   const isT = env.isStoredTrueFact(fact.params, tmp);
    //   if (!isT) return hInfo(RType.ProveFailed, `${fact.name} not satisfied.`);
    // }

    return hInfo(RType.ProveTrue);
  } catch (error) {
    return hRunErr(env, RType.ProveError);
  }
}

// function proveInferExec(env: L_Env, node: YAProveNode, relatedT: TNode): RInfo {
//   try {
//     // const onlyIfs = node.onlyIfExprs as L_Node[];
//     // const req: CallOptNode[] = node.opt.req;
//     // const newEnv = new L_Env();
//     // newEnv.father = env;
//     // env = newEnv;

//     // const relOpt = CallOptNode.create(
//     //   node.opt.optName,
//     //   node.opt.optParams.map((ls) =>
//     //     ls.map((s) => (s.startsWith("*") ? s.slice(1) : s))
//     //   )
//     // );
//     // const TFixFree = fixFree(env, relOpt, true, true, relatedT);
//     // if (!TFixFree) return hRunErr(env, RType.ProveError);

//     // /**Declare variables in newEnv */
//     // for (let varToDecl of node.opt.optParams.flat()) {
//     //   if (varToDecl.startsWith("*") || newEnv.declaredVars.includes(varToDecl))
//     //     continue;
//     //   newEnv.declareNewVar(varToDecl);
//     // }

//     // /**Emit req in newEnv */
//     // for (const [i, fact] of req.entries()) {
//     //   const tmp = env.getRelT(fact.optName);
//     //   if (!tmp)
//     //     return hRunErr(env, RType.ProveError, `${fact.optName} not declared`);
//     //   newEnv.newStoredFact(fact.optParams, tmp, [], []);
//     // }

//     // /**Execute onlyIfs in the prove block*/
//     // for (const [i, curNode] of onlyIfs.entries()) {
//     //   const res = nodeExec(newEnv, curNode);
//     //   if (!RInfoIsTrue(res))
//     //     return hInfo(RType.ProveFailed, `${i}th stmt failed.`);
//     // }

//     // /**After execution, check whether template onlyIfs are satisfied.*/
//     // for (const [i, fact] of TFixFree.onlyIf.entries()) {
//     //   const tmp = env.getRelT(fact.name);
//     //   if (!tmp)
//     //     return hRunErr(env, RType.ProveError, `${fact.name} not declared`);
//     //   const isT = env.isStoredTrueFact(fact.params, tmp);
//     //   if (!isT) return hInfo(RType.ProveFailed, `${fact.name} not satisfied.`);
//     // }

//     return hInfo(RType.ProveTrue);
//   } catch (error) {
//     return hRunErr(env, RType.ProveError);
//   }
// }

/**
 * Proves inference execution by building a new environment, checking requirements,
 * and validating conditions based on relational terms and call options.
 *
 * Steps:
 * 1. Build a new environment (`newEnv`).
 * 2. Check if the given requirements (from `relT` or `callOpt`) contain any variables that
 *    do not start with `#`. If any variables start with `#`, emit the requirement in `newEnv`.
 * 3. Run `proveBlock`. If no errors occur, proceed to the next step.
 * 4. If no errors occur, check whether all `onlyIf` conditions (from `relT` and `callOpt`)
 *    are satisfied.
 * 5. If all `onlyIf` conditions are satisfied, emit the corresponding conditions
 *    from `relT` and `callOpt`.
 */
function proveInferExec(env: L_Env, node: YAProveNode, relT: TNode): RInfo {
  try {
    const newEnv = new L_Env(env);
    const proveHashParams: string[] = node.opt.optParams
      .map((ls) =>
        ls.reduce((acc, s) => {
          if (s.startsWith("#")) {
            acc.push(s.slice(1));
          }
          return acc;
        }, [] as string[])
      )
      .flat();
    const proveNoHashParams: string[][] = node.opt.optParams.map((ls) =>
      ls.map((s) => (s.startsWith("#") ? s.slice(1) : s))
    );

    /**
     * Check or emit requirements from callOpt before doing so from relT,
     * so that user can suppose req of relT is True.
     * */
    for (const req of node.opt.req) {
      if (req.optParams.flat().every((s) => !proveHashParams.includes(s))) {
        const out = callOptExec(env, req);
        if (!RInfoIsTrue(out))
          return hInfo(RType.Unknown, `${req.toString()} unsatisfied.`);
      } else {
        newEnv.YANewFactEmit(req, false);
      }
    }

    // Check or emit requirements from relT
    let { v: fixedOpts, err } = fixOpt(
      env,
      proveNoHashParams,
      relT.getSelfFathersFreeVars(),
      relT.getSelfFathersReq()
    );
    if (isNull(fixedOpts)) return hRunErr(env, RType.Error, err);
    for (const req of fixedOpts) {
      if (req.optParams.every((ls) => ls.every((s) => s.startsWith("#")))) {
        const out = callOptExec(env, req);
        if (!RInfoIsTrue(out))
          return hInfo(RType.Unknown, `${req.toString()} unsatisfied.`);
      } else {
        newEnv.YANewFactEmit(req, false);
      }
    }

    // Run proveBlock
    for (const expr of node.proveBlock) {
      const out = nodeExec(newEnv, expr);
      if (RInfoIsError(out)) return out;
    }

    // check onlyIF of opt
    for (const onlyIf of node.opt.onlyIFs) {
      if (env.yaDefCheckEmit(onlyIf, true)) continue;
      else {
        return hInfo(RType.Unknown, `${onlyIf.toString()} unknown.`);
      }
    }

    // check onlyIf of relT
    let tmp = fixOpt(
      env,
      node.opt,
      relT.getSelfFathersFreeVars(),
      relT.onlyIfExprs as CallOptNode[]
    );
    if (isNull(tmp.v)) return hRunErr(env, RType.Error, tmp.err);
    for (const onlyIf of tmp.v) {
      if (env.yaDefCheckEmit(onlyIf, true)) continue;
      else {
        return hInfo(RType.Unknown, `${onlyIf.toString()} unknown.`);
      }
    }

    // emit prove, notice how opt of proveNode is literally the same as the fact emitted
    knowExec(env, new KnowNode([node.opt]));

    return hInfo(RType.ProveTrue);
  } catch (error) {
    return hRunErr(env, RType.ProveError);
  }
}
