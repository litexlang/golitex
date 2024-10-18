import { isNull } from "lodash";
import {
  CallOptNode,
  KnowNode,
  L_Node,
  // L_NodeType,
  LetNode,
  TNode,
  ProveNode,
  HaveNode,
  ExistNode,
  DefNode,
  InferNode,
  ByNode,
  ThmNode,
  FactNode,
  ShortCallOptNode,
  yaIfThenNode,
  yaFactNode,
  OrNode,
  DeclNode,
  DefDeclNode,
} from "./ast";
import { L_Keywords } from "./common";
import { L_Env } from "./env";
import {
  cEnvRType,
  ErrL_Out,
  fixOpt,
  isL_OutErr,
  UdfErr,
  RL_Out,
  hRemoveHashPrefix,
  isRTypeErr,
  isRTypeTrue,
} from "./shared";
import { only } from "node:test";
import { error } from "console";

export enum RType {
  Error,
  True, // not only used as True for callInferExec, but also as a generic type passed between subFunctions.
  // KnowTrue,
  // KnowError,
  KnowUndeclared,
  // DefTrue,
  // DefError,
  // InferTrue,
  // InferError,
  False,
  Unknown,
  // Error,
  // HaveTrue,
  HaveFailed,
  // LetTrue,
  // LetError,
  // Error,
  // ProveTrue,
  ProveFailed,
  // KnowEverythingTrue,
  // KnowEverythingError,
  // ExistError,
  // ExistTrue,
  // ByError,
  // ByTrue,
  // ThmTrue,
  ThmFailed,
  // ThmError,
}

export const RTypeMap: { [key in RType]: string } = {
  [RType.Error]: "error",
  [RType.False]: "check: false",
  [RType.True]: "check: true",
  [RType.Unknown]: "check: unknown",
  // [RType.KnowTrue]: "",
  // [RType.DefTrue]: "",
  // [RType.KnowError]: "know: error",
  // [RType.DefError]: "def: error",
  // [RType.InferError]: "infer: error",
  // [RType.InferTrue]: "",
  [RType.KnowUndeclared]: "know: undeclared opt",
  // [RType.HaveError]: "have: error",
  // [RType.HaveTrue]: "have: true",
  [RType.HaveFailed]: "have: failed",
  // [RType.LetError]: "let: error",
  // [RType.LetTrue]: "",
  // [RType.ProveError]: "prove: error",
  // [RType.ProveTrue]: "prove: true",
  [RType.ProveFailed]: "prove: failed",
  // [RType.KnowEverythingError]: "know_everything: error",
  // [RType.KnowEverythingTrue]: "know_everything: true",
  // [RType.ExistError]: "exist: error",
  // [RType.ExistTrue]: "exist: true",
  // [RType.ByError]: "by: error",
  // [RType.ByTrue]: "by: true",
  // [RType.ThmError]: "thm: error",
  [RType.ThmFailed]: "thm: failed",
  // [RType.ThmTrue]: "thm: true",
};

export function hRunErr(env: L_Env, type: RType, message: string | null = "") {
  env.newMessage(RTypeMap[type] + ": " + message);
}

export const hInfo = (t: RType, s: string = "") => {
  return { type: t, message: s };
};
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

const nodeExecMap: { [key: string]: (env: L_Env, node: any) => RType } = {
  DefNode: declExec,
  DefDeclNode: declExec,
  ExistNode: declExec,
  KnowNode: knowExec,
  LetNode: letExec,
  ProveNode: proveExec,
  HaveNode: haveExec,
  ByNode: byExec,
  ThmNode: thmExec,
};

export function nodePrintExec(env: L_Env, node: L_Node): RType {
  try {
    const nodeType = node.constructor.name;
    const execFunc = nodeExecMap[nodeType];

    if (execFunc && isRTypeTrue(execFunc(env, node)))
      return successMesIntoEnv(env, node);
    else {
      const result = callOptExec(env, node as CallOptNode);
      if (isRTypeTrue(result)) return successMesIntoEnv(env, node);
      else if (result === RType.Unknown) {
        env.newMessage(`Unknown ${node.toString()}`);
        return RType.Unknown;
      } else if (result === RType.False) {
        env.newMessage(`False ${node.toString()}`);
        return RType.False;
      }
    }

    return RType.Error;
  } catch (error) {
    return RType.Error;
  }

  function successMesIntoEnv(env: L_Env, node: L_Node): RType {
    env.newMessage(`OK! ${node.toString()}`);
    return RType.True;
  }
}

export function nodeExec(env: L_Env, node: L_Node): RType {
  try {
    if (node instanceof DeclNode) {
      return declExec(env, node as DeclNode);
    } else if (node instanceof KnowNode) {
      return knowExec(env, node as KnowNode);
    } else if (node instanceof LetNode) {
      return letExec(env, node as LetNode);
    } else if (node instanceof ProveNode) {
      return proveExec(env, node as ProveNode);
    } else if (node instanceof HaveNode) {
      return haveExec(env, node as HaveNode);
    } else if (node instanceof ByNode) {
      return byExec(env, node as ByNode);
    } else if (node instanceof ThmNode) {
      return thmExec(env, node as ThmNode);
    }
    return RType.Error;
  } catch (error) {
    return RType.Error;
  }
}

function letExec(env: L_Env, node: LetNode): RType {
  try {
    // Check ofr duplicate variable declarations
    const notDeclared = node.vars.filter((v) => env.declaredVars.includes(v));
    if (!notDeclared) {
      return cEnvRType(
        env,
        RType.Error,
        `Error: Variable(s) ${node.vars.join(", ")} already declared in this scope.`
      );
    }

    env.declaredVars = env.declaredVars.concat(node.vars) as string[];

    knowExec(env, new KnowNode(node.facts));

    // for (let i = 0; i < node.facts.length; i++) {
    //   //! In theory, ANY FactNode can be known, but currently knowExec is not refactored.
    // if (node.properties[i] instanceof CallOptNode) {
    //   let info = knowFactExec(env, node.properties[i] as CallOptNode);
    //   if (isNull(info)) return cEnvRType(env, RType.Error);
    // }
    // }

    return RType.True;
  } catch (error) {
    return cEnvRType(env, RType.Error, "let");
  }
}

function callOptExec(env: L_Env, fact: CallOptNode): RType {
  const relT = env.getRelT(fact as CallOptNode);
  if (!relT)
    return cEnvRType(env, RType.Error, `${fact.optName} is not declared.`);
  let info = RType.Error;
  if (relT instanceof ExistNode) {
    info = callExistExec(env, fact, relT);
  } else if (relT instanceof DefNode) {
    info = callDefExec(env, fact, relT);
  } else if (relT instanceof InferNode) {
    info = callInferExec(env, fact, relT);
  }
  if (info === RType.Unknown || info === RType.False) {
    return info;
  }
  if (isRTypeErr(info)) return cEnvRType(env, RType.Error, "");
  return RType.True;
}

// function callOptsExec(env: L_Env, node: CallOptsNode): RType {
//   try {
//     const whatIsTrue: string[] = [];
//     for (const fact of (node as CallOptsNode).nodes) {
//       const info = callOptExec(env, fact as CallOptNode);
//       if (info.v === RType.Unknown || info.v === RType.False) {
//         return (info.v)
//       } else if (isNull(info.v)) {
//         return (null);
//         whatIsTrue.push(info.err);
//       }
//     }
//     return (RType.True)
//   } catch (error) {
//     return cEnvRType(env, RType.Error, "call operators");
//   }
// }

/**
 * Steps
 * 1. check opt itself
 * 2. check opt requirements
 * 3. If 1. and 2. true, emit onlyIfs of relT
 */
function callInferExec(env: L_Env, node: CallOptNode, relT: InferNode): RType {
  try {
    if (!env.checkEmit(node, false).v) return RType.Unknown;

    let isT = relT.checkReq(env, node);
    if (isRTypeErr(isT)) return cEnvRType(env, RType.Error);

    if (isT === RType.True) {
      return relT.emitTOnlyIf(env, node);
    } else {
      return RType.Unknown;
    }
  } catch (error) {
    return cEnvRType(env, RType.Error, `call ${node.optName}`);
  }
}

// function declExec(env: L_Env, node: TNode): RType {
//   try {
//     // Check if the template name already exists
//     if (!node.isRedefine && env.declaredTemplates.has(node.name)) {
//       return cEnvRType(env, RType.Error, `${node.name} has declared`);
//     }

//     if (L_Keywords.includes(node.name)) {
//       return cEnvRType(env, RType.Error, `'${node.name}' is keyword.`);
//     }

//     // If not already declared, set the new template
//     env.declaredTemplates.set(node.name, node);

//     // move templates(pure, questionMark) from node.onlyIfs to node.declaredTemplates
//     let res = node.initDeclaredTemplates(env);
//     if (isRTypeErr(res)) return cEnvRType(env, RType.Error);

//     return RType.True;
//   } catch (error) {
//     return cEnvRType(env, RType.Error);
//   }
// }

function declExec(env: L_Env, node: DeclNode): RType {
  try {
    env.declTemp(node.name, node);

    return RType.True;
  } catch (error) {
    let m = `'${node.toString()}'`;
    if (error instanceof Error) m += ` ${error.message}`;
    yaHandleExecError(env, m);
    throw error;
  }
}

// function knowExec(env: L_Env, node: KnowNode): RType {
//   try {
//     let facts: FactNode[] = [];
//     let isKnowEverything: Boolean = false;
//     let res: RType = RType.Error;

//     if (node instanceof KnowNode) {
//       facts = (node as KnowNode).facts;
//       isKnowEverything = (node as KnowNode).isKnowEverything;
//     }

//     for (const fact of facts) {
//       if (fact instanceof CallOptNode) {
//         if (isKnowEverything) {
//           res = knowEverythingCallOptExec(env, fact);
//         } else {
//           res = knowFactExec(env, fact);
//         }
//       }
//       // The commented-out ImpliesCallOptNode case has been omitted
//       if (isRTypeErr(res)) return res;
//     }

//     return RType.True;
//   } catch (error) {
//     return cEnvRType(env, RType.Error, "know");
//   }
// }

function knowEverythingCallOptExec(env: L_Env, fact: CallOptNode): RType {
  try {
    return RType.True;
  } catch (error) {
    return cEnvRType(env, RType.Error, "");
  }
}

//! node here must be changed into type FactNode
function knowFactExec(env: L_Env, node: CallOptNode): RType {
  try {
    if (!env.getRelT(node)) return RType.Error;

    if (
      !node.optParams.every((ls) =>
        ls.every((s) => env.declaredVars.includes(s) || s.startsWith("#"))
      )
    )
      return cEnvRType(env, RType.Error, "symbol not declared.");

    if (node.optParams.every((ls) => ls.every((s) => s[0] !== "#")))
      // If every var in callOpt is not 'forall', we emit onlyIf immediately
      env.newFactEmit(node);
    else env.newFactEmit(node, false);

    // env.newFactEmit()
    return RType.True;
  } catch (error) {
    return cEnvRType(env, RType.Error);
  }
}

/**
 * Steps
 * 1. Check whether given vars(symbols) already declared
 * 2. Check whether have.opt.isTrue
 * 3. If true, emit have.opt along with its onlyIfs
 */
function haveExec(env: L_Env, node: HaveNode): RType {
  try {
    const relT = env.relT(node.opt).v;
    if (!(relT instanceof ExistNode))
      return cEnvRType(
        env,
        RType.Error,
        `${node.opt.toString()} is not exist operator.`
      );

    if (relT.isTrue || (relT.isTrue = existTrue(env, node.opt.optName))) {
      const isT = node.vars.every((e) => !env.declaredVars.includes(e));
      if (!isT)
        return cEnvRType(
          env,
          RType.Error,
          `One of ${node.vars.toString()} already declared.`
        );
      else {
        node.vars.forEach((e) => env.newVar(e));
        env.newFactEmit(node.opt, true);
        return RType.True;
      }
    }

    return RType.HaveFailed;
  } catch (error) {
    return cEnvRType(env, RType.Error);
  }

  function existTrue(env: L_Env, optName: string) {
    const facts = env.facts.get(optName);
    if (!facts) return false;
    for (const fact of facts) {
      if (
        fact.optParams.every((e) => e.every((v) => !v.startsWith("#"))) &&
        fact.req.every((e) => env.checkEmit(e, false))
      )
        return true;
    }
    return false;
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
    cEnvRType(env, RType.Error, "exist not declared");
    return undefined;
  }

  const mapping = relT?.fix(opt);
  if (!mapping) {
    cEnvRType(env, RType.Error, "calling undeclared symbol.");
    return undefined;
  }

  if (fixReq) {
    const optParamsArr: OptParamsType[] = [];
    for (let curOpt of relT.requirements as CallOptNode[]) {
      const fixedArrArr = _fixFreesUsingMap(mapping, curOpt.optParams);
      if (!fixedArrArr) {
        cEnvRType(env, RType.Error);
        return undefined;
      }
      optParamsArr.push({ name: curOpt.optName, params: fixedArrArr });
    }
    result.req = optParamsArr;
  }

  if (fixOnlyIf) {
    const optParamsArr: OptParamsType[] = [];
    for (let curOpt of relT.onlyIfs as CallOptNode[]) {
      const fixedArrArr = _fixFreesUsingMap(mapping, curOpt.optParams);
      if (!fixedArrArr) {
        cEnvRType(env, RType.Error);
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
        cEnvRType(env, RType.Error);
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

function callExistExec(env: L_Env, node: CallOptNode, relT: ExistNode): RType {
  try {
    const out = env.checkEmit(node, true);
    if (out.v) {
      // relT.isTrue = true is updated in haveExec
      return RType.True;
    } else {
      return RType.Unknown;
    }
  } catch (error) {
    return cEnvRType(env, RType.Error);
  }
}

/**
 * Steps
 * 1. check itself.If true, emit its req
 * 2. If unknown, check its req; if true this time, emit itself
 */
function callDefExec(env: L_Env, node: CallOptNode, relT: DefNode): RType {
  try {
    if (env.checkEmit(node, true).v) {
      return RType.True;
    } else {
      const out = relT.checkReq(env, node);
      if (out === RType.True) relT.emitTOnlyIf(env, node);
      return out;
    }
  } catch (error) {
    return cEnvRType(env, RType.Error);
  }
}

function proveExec(env: L_Env, node: ProveNode): RType {
  try {
    const relatedT = env.getRelT(node.opt.optName);
    if (relatedT instanceof InferNode) {
      return proveInferExec(env, node, relatedT);
    } else if (relatedT instanceof DefNode) {
      return proveDefExec(env, node, relatedT);
    }

    return cEnvRType(
      env,
      RType.Error,
      `prove keyword should be followed by declared template name`
    );
  } catch (error) {
    return cEnvRType(env, RType.Error);
  }
}

/**
 * Proves inference execution.
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
function proveInferExec(env: L_Env, node: ProveNode, relT: TNode): RType {
  try {
    const newEnv = new L_Env(env);
    const proveHashParams: string[] = [];
    const proveNoHashParams: string[][] = node.opt.optParams.map((ls) =>
      ls.map((s) => {
        if (s.startsWith("#")) {
          proveHashParams.push(s.slice(1));
          return s.slice(1);
        } else return s;
      })
    );

    /**
     * Check or emit requirements from callOpt before doing so from relT,
     * so that user can suppose req of relT is True.
     * */
    for (const req of node.opt.req) {
      if (req.optParams.flat().every((s) => !proveHashParams.includes(s))) {
        const out = env.checkEmit(req, false);
        if (isNull(out.v)) return RType.Unknown;
      } else {
        newEnv.newFactEmit(req, false);
      }
    }

    // Check or emit requirements from relT
    let { v: fixedOpts, err } = fixOpt(
      env,
      proveNoHashParams,
      relT.allVars(),
      relT.allReq()
    );
    if (isNull(fixedOpts)) return cEnvRType(env, RType.Error, err);
    for (const req of fixedOpts) {
      if (req.optParams.every((ls) => ls.every((s) => s.startsWith("#")))) {
        const out = env.checkEmit(req, false);
        if (isNull(out.v)) return RType.Unknown;
      } else {
        newEnv.newFactEmit(req, false);
      }
    }

    // Run proveBlock
    for (const expr of node.proveBlock) {
      const out = nodeExec(newEnv, expr);
      if (isRTypeErr(out)) return out;
    }

    // check and emit onlyIF of opt
    for (const onlyIf of node.opt.onlyIFs) {
      if (newEnv.checkEmit(onlyIf, true, env).v) continue;
      else {
        return RType.Unknown;
      }
    }

    // check and emit onlyIf of relT
    let tmp = fixOpt(
      env,
      node.opt,
      relT.allVars(),
      relT.onlyIfs as CallOptNode[]
    );
    if (isNull(tmp.v)) return cEnvRType(env, RType.Error, tmp.err);
    for (const onlyIf of tmp.v) {
      if (newEnv.checkEmit(onlyIf, true, env)) continue;
      else {
        return RType.Unknown;
      }
    }

    // emit prove.opt itself, notice how opt of proveNode is literally the same as the fact emitted
    knowFactExec(env, node.opt);

    if (node.name !== "") env.newBy(node.name, node.opt);

    return RType.True;
  } catch (error) {
    return cEnvRType(env, RType.Error);
  }
}

/**
 * Proves def execution.
 *
 * Steps:
 * 1. Build a new environment (`newEnv`).
 * 2. Check if the given requirements (`callOpt`) contain any variables that
 *    do not start with `#`. If any variables start with `#`, emit the requirement in `newEnv`.
 * 3. Run `proveBlock`. If no errors occur, proceed to the next step.
 * 4. If no errors occur, check whether all `req` conditions (from `relT`)
 *    are satisfied.
 * 5. If all `req` conditions are satisfied, emit the corresponding opt.
 */
function proveDefExec(env: L_Env, node: ProveNode, relT: TNode): RType {
  try {
    const newEnv = new L_Env(env);

    if (
      !node.opt.optParams
        .flat()
        .every((e) => (e.startsWith("#") ? true : env.declaredVars.includes(e)))
    ) {
      const vars = node.opt.optParams.map((ls) => ls.join(",")).join(",");
      return cEnvRType(env, RType.Error, `Some of [${vars}] undeclared.`);
    }

    const proveHashParams: string[] = [];

    // If parameter start with #, we push s.slice(1); else push s
    const proveNoHashParams: string[][] = node.opt.optParams.map((ls) =>
      ls.map((s) => {
        if (s.startsWith("#")) {
          proveHashParams.push(s.slice(1));
          return s.slice(1);
        } else return s;
      })
    );

    /**
     * Check or emit requirements from callOpt before doing so from relT,
     * so that user can suppose req of relT is True.
     * */
    for (const req of node.opt.req) {
      if (req.optParams.flat().every((s) => !proveHashParams.includes(s))) {
        const out = env.checkEmit(req, false);
        if (isNull(out.v)) return RType.Unknown;
      } else {
        newEnv.newFactEmit(req, false);
      }
    }

    // Run proveBlock
    for (const expr of node.proveBlock) {
      const out = nodeExec(newEnv, expr);
      if (isRTypeErr(out)) return out;
    }

    // Check requirements from relT
    let { v: fixedOpts, err } = fixOpt(
      env,
      proveNoHashParams,
      relT.allVars(),
      relT.allReq()
    );
    if (isNull(fixedOpts)) return cEnvRType(env, RType.Error, err);
    for (const req of fixedOpts) {
      const out = newEnv.checkEmit(req, false);
      if (isNull(out.v)) return RType.Error;
      if (out.v === false) return RType.Unknown;
    }

    // check and emit onlyIF of opt
    for (const onlyIf of node.opt.onlyIFs) {
      if (newEnv.checkEmit(onlyIf, true, env)) continue;
      else {
        return RType.Unknown;
      }
    }

    // check and emit onlyIf of relT
    let tmp = fixOpt(
      env,
      node.opt,
      relT.allVars(),
      relT.onlyIfs as CallOptNode[]
    );
    if (isNull(tmp.v)) return cEnvRType(env, RType.Error, tmp.err);
    for (const onlyIf of tmp.v) {
      if (newEnv.checkEmit(onlyIf, true, env)) continue;
      else {
        return RType.Unknown;
      }
    }

    // emit prove, notice how opt of proveNode is literally the same as the fact emitted
    knowFactExec(env, node.opt);

    if (node.name !== "") env.newBy(node.name, node.opt);

    return RType.True;
  } catch (error) {
    return cEnvRType(env, RType.Error);
  }
}

function byExec(env: L_Env, node: ByNode): RType {
  try {
    const freeFact = env.bys.get(node.name);
    if (freeFact === undefined) return cEnvRType(env, RType.Error);

    const mapping = env.useSingleFreeFactToCheck(freeFact, node.opt);

    if (mapping === UdfErr) return RType.Unknown;
    else return RType.True;
  } catch (error) {
    return cEnvRType(env, RType.Error);
  }
}

/**
 * Steps
 * 1. extract template from thm and declare it
 * 2. prove opt extracted from thm, everything works as if proveExec
 */
function thmExec(env: L_Env, node: ThmNode): RType {
  try {
    // extract template from thm
    // const freeVars = hRemoveHashPrefix(node.opt.optParams);

    // const relT = new InferNode(
    //   node.opt.optName,
    //   freeVars[0],
    //   node.opt.req,
    //   node.opt.onlyIFs
    // );
    // let isT = declExec(env, relT);

    // if (isT !== RType.True) return cEnvRType(env, RType.Error);

    // isT = proveInferExec(env, new ProveNode(node.opt, node.proveBlock), relT);
    // if (isT !== RType.True) return RType.ThmFailed;

    return RType.True;
  } catch (error) {
    return cEnvRType(env, RType.Error);
  }
}

function knowExec(env: L_Env, node: KnowNode): RType {
  try {
    for (const fact of node.facts) {
      if (fact instanceof ShortCallOptNode) {
        const relT = env.getDeclTemp(fact.fullName);
        if (relT === undefined) throw Error(`${fact.fullName} not declared.`);
        const isT = env.varsAreNotDeclared(fact.params.flat());
        if (isT) throw Error(`${fact.params.flat().toString()} not declared.`);
        env.addShortOptFact(env, fact);
      } else if (fact instanceof yaIfThenNode) {
        //! Here have 2 situations: if-then with name, if-then with no name
        for (const onlyIf of fact.onlyIfs) {
          env.addShortOptFact(env, onlyIf, fact.req, fact.freeVars);
        }
      }
    }

    return RType.True;
  } catch (error) {
    let m = `'${node.toString()}'`;
    if (error instanceof Error) m += ` ${error.message}`;
    yaHandleExecError(env, m);
    throw error;
  }
}

function yaHandleExecError(env: L_Env, m: string) {
  env.newMessage(m);
}

function isFactDeclared(env: L_Env, fact: yaFactNode): Boolean {
  if (fact instanceof ShortCallOptNode) {
    return env.relT(fact.fullName).v !== null;
  } else if (fact instanceof yaIfThenNode) {
    return (
      fact.req.every((e) => isFactDeclared(env, e)) &&
      fact.onlyIfs.every((e) => isFactDeclared(env, e))
    );
  } else if (fact instanceof OrNode) {
    return fact.facts.every((e) => isFactDeclared(env, e));
  }

  throw error;
}
