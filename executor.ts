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
  ProveNode,
  HaveNode,
  ExistNode,
  DefNode,
  InferNode,
} from "./ast";
import { L_Keywords } from "./common";
import { L_Env } from "./env";
import {
  cEnvErrL_Out,
  cL_Out,
  ErrL_Out,
  fixOpt,
  isL_OutErr,
  RL_Out,
} from "./shared";

export enum RType {
  True, // not only used as True for callInferExec, but also as a generic type passed between subFunctions.
  KnowTrue,
  KnowError,
  KnowUndeclared,
  DefTrue,
  DefError,
  InferTrue,
  InferError,
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
  ByError,
  ByTrue,
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
  [RType.InferError]: "infer: error",
  [RType.InferTrue]: "infer: true",
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
  [RType.ByError]: "by: error",
  [RType.ByTrue]: "by: true",
};

function IsL_OutRTypeErr(res: RL_Out) {
  function isErrorRType(type: RType): boolean {
    const typeName = RType[type]; // 获取枚举的键名
    return typeName.endsWith("Error");
  }

  return isErrorRType(res.v as RType);
}

export function hRunErr(env: L_Env, type: RType, message: string | null = "") {
  env.pushNewError(RTypeMap[type] + ": " + message);
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

export function nodeExec(env: L_Env, node: L_Node): RL_Out {
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
        return proveExec(env, node as ProveNode);
      case L_NodeType.HaveNode:
        return haveExec(env, node as HaveNode);
    }
    return cEnvErrL_Out(env, RType.Error, "Stmt");
  } catch (error) {
    return cEnvErrL_Out(env, RType.Error, "Stmt");
  }
}

function letExec(env: L_Env, node: LetNode): RL_Out {
  try {
    // Check ofr duplicate variable declarations
    const notDeclared = node.vars.filter((v) => env.declaredVars.includes(v));
    if (!notDeclared) {
      return cEnvErrL_Out(
        env,
        RType.LetError,
        `Error: Variable(s) ${node.vars.join(", ")} already declared in this scope.`
      );
    }

    env.declaredVars = env.declaredVars.concat(node.vars) as string[];

    for (let i = 0; i < node.properties.length; i++) {
      let info = knowCallOptExec(env, node.properties[i]);
      if (isNull(info.v)) return cEnvErrL_Out(env, RType.LetError, info.err);
    }

    return cL_Out(RType.LetTrue, node.toString());
  } catch (error) {
    return cEnvErrL_Out(env, RType.LetError, "let");
  }
}

function callOptExec(env: L_Env, fact: CallOptNode): RL_Out {
  const relT = env.getRelT(fact as CallOptNode);
  if (!relT)
    return cEnvErrL_Out(env, RType.Error, `${fact.optName} is not declared.`);
  let info: RL_Out = cL_Out(RType.Error);
  switch (relT.type) {
    case L_NodeType.ExistNode:
      info = callExistExec(env, fact, relT as ExistNode);
      break;
    case L_NodeType.DefNode:
      info = callDefExec(env, fact, relT as DefNode);
      break;
    case L_NodeType.InferNode:
      info = callInferExec(env, fact, relT as InferNode);
      break;
  }
  if (info.v === RType.Unknown || info.v === RType.False) {
    return info;
  }
  if (isL_OutErr(info)) return cEnvErrL_Out(env, RType.Error, "");
  return cL_Out(RType.True, fact.toString());
}

function callOptsExec(env: L_Env, node: CallOptsNode): RL_Out {
  try {
    const whatIsTrue: string[] = [];
    for (const fact of (node as CallOptsNode).nodes) {
      const info = callOptExec(env, fact);
      if (info.v === RType.Unknown || info.v === RType.False) {
        return cL_Out(info.v);
      } else if (isNull(info.v)) {
        return cL_Out(null);
      } else {
        whatIsTrue.push(info.err);
      }
    }
    return cL_Out(RType.True, whatIsTrue.join(";"));
  } catch (error) {
    return cEnvErrL_Out(env, RType.Error, "call operators");
  }
}

/**
 * Steps
 * 1. check opt itself
 * 2. check opt requirements
 * 3. If 1. and 2. true, emit onlyIfs of relT
 */
function callInferExec(env: L_Env, node: CallOptNode, relT: InferNode): RL_Out {
  try {
    if (!env.checkEmit(node, false)) {
      return cL_Out(RType.Unknown, `${node.toString()} itself unknown`);
    }

    let isT = relT.checkReq(env, node).v;
    if (isNull(isT)) return cL_Out(RType.Error);

    if (isT === RType.True) {
      return relT.emitTOnlyIf(env, node);
    } else {
      return cL_Out(RType.Unknown);
    }
  } catch (error) {
    return cEnvErrL_Out(env, RType.Error, `call ${node.optName}`);
  }
}

function templateDeclExec(env: L_Env, node: TNode): RL_Out {
  try {
    // Check if the template name already exists
    if (!node.isRedefine && env.declaredTemplates.has(node.name)) {
      return cEnvErrL_Out(env, RType.DefError, `${node.name} has declared`);
    }

    if (L_Keywords.includes(node.name)) {
      return cEnvErrL_Out(env, RType.DefError, `'${node.name}' is keyword.`);
    }

    // If not already declared, set the new template
    env.declaredTemplates.set(node.name, node);

    // move templates(pure, questionMark) from node.onlyIfs to node.declaredTemplates
    let res = node.initDeclaredTemplates(env);
    if (isNull(res.v)) return cEnvErrL_Out(env, RType.DefError);

    switch (node.type) {
      case L_NodeType.DefNode:
        return cL_Out(RType.DefTrue, `def ${node.toString()}`);
      case L_NodeType.ExistNode:
        return cL_Out(RType.DefTrue, `exist ${node.toString()}`);
      case L_NodeType.InferNode:
        return cL_Out(RType.DefTrue, `infer ${node.toString()}`);
    }

    return cL_Out(RType.Error);
  } catch (error) {
    return cEnvErrL_Out(env, RType.DefError);
  }
}

function knowExec(env: L_Env, node: KnowNode): RL_Out {
  try {
    let facts: CanBeKnownNode[] = [];
    let isKnowEverything: Boolean = false;
    let res: RL_Out = { v: RType.Error, err: "" };

    if (node.type === L_NodeType.KnowNode) {
      facts = (node as KnowNode).facts;
      isKnowEverything = (node as KnowNode).isKnowEverything;
    }

    for (const fact of facts) {
      switch (fact.type) {
        case L_NodeType.CallOptNode:
          if (isKnowEverything)
            res = knowEverythingCallOptExec(env, fact as CallOptNode);
          else res = knowCallOptExec(env, fact as CallOptNode);
          break;
        // case L_NodeType.ImpliesFactNode:
        //   res = knowImpliesFactExec(env, fact as ImpliesFactNode);
        //   break;
        case L_NodeType.DefNode:
        case L_NodeType.InferNode: {
          res = templateDeclExec(env, fact as TNode);
          if (isKnowEverything) {
            res = knowEverythingCallOptExec(
              env,
              CallOptNode.create((fact as TNode).name, [
                (fact as TNode).freeVars,
              ])
            );
          } else {
            res = knowCallOptExec(
              env,
              CallOptNode.create((fact as TNode).name, [
                (fact as TNode).freeVars,
              ])
            );
          }
          break;
        }
      }
      if (isNull(res.v)) return res;
    }

    return cL_Out(RType.KnowTrue);
  } catch (error) {
    return cEnvErrL_Out(env, RType.KnowError, "know");
  }
}

function knowEverythingCallOptExec(env: L_Env, fact: CallOptNode): RL_Out {
  try {
    return cL_Out(RType.KnowTrue);
  } catch (error) {
    return cEnvErrL_Out(env, RType.KnowEverythingError, "");
  }
}

function knowCallOptExec(env: L_Env, node: CallOptNode): RL_Out {
  try {
    if (!env.getRelT(node)) return cL_Out(RType.KnowError);

    if (
      !node.optParams.every((ls) =>
        ls.every((s) => env.declaredVars.includes(s) || s.startsWith("#"))
      )
    )
      return cEnvErrL_Out(env, RType.KnowError, "symbol not declared.");

    if (node.optParams.every((ls) => ls.every((s) => s[0] !== "#")))
      // If every var in callOpt is not 'forall', we emit onlyIf immediately
      env.newFactEmit(node);
    else env.newFactEmit(node, false);

    // env.newFactEmit()
    return cL_Out(RType.KnowTrue);
  } catch (error) {
    return cEnvErrL_Out(env, RType.KnowError);
  }
}

/**
 * Steps
 * 1. Check whether given vars(symbols) already declared
 * 2. Check whether have.opt.isTrue
 * 3. If true, emit have.opt along with its onlyIfs
 */
function haveExec(env: L_Env, node: HaveNode): RL_Out {
  try {
    const relT = env.relT(node.opt).v;
    if (!(relT instanceof ExistNode))
      return cEnvErrL_Out(
        env,
        RType.HaveError,
        `${node.opt.toString()} is not exist operator.`
      );

    if (relT.isTrue || (relT.isTrue = existTrue(env, node.opt.optName))) {
      const isT = node.vars.every((e) => !env.declaredVars.includes(e));
      if (!isT)
        return cEnvErrL_Out(
          env,
          RType.HaveError,
          `One of ${node.vars.toString()} already declared.`
        );
      else {
        node.vars.forEach((e) => env.newVar(e));
        env.newFactEmit(node.opt, true);
        return cL_Out(RType.HaveTrue);
      }
    }

    return cL_Out(RType.HaveFailed);
  } catch (error) {
    return cEnvErrL_Out(env, RType.HaveError);
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
    cEnvErrL_Out(env, RType.Error, "exist not declared");
    return undefined;
  }

  const mapping = relT?.fix(opt);
  if (!mapping) {
    cEnvErrL_Out(env, RType.Error, "calling undeclared symbol.");
    return undefined;
  }

  if (fixReq) {
    const optParamsArr: OptParamsType[] = [];
    for (let curOpt of relT.requirements as CallOptNode[]) {
      const fixedArrArr = _fixFreesUsingMap(mapping, curOpt.optParams);
      if (!fixedArrArr) {
        cEnvErrL_Out(env, RType.Error);
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
        cEnvErrL_Out(env, RType.Error);
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
        cEnvErrL_Out(env, RType.Error);
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

function callExistExec(env: L_Env, node: CallOptNode, relT: ExistNode): RL_Out {
  try {
    const out = env.checkEmit(node, true);
    if (out.v) {
      // relT.isTrue = true is updated in haveExec
      return cL_Out(RType.ExistTrue);
    } else {
      return cL_Out(RType.Unknown);
    }
  } catch (error) {
    return cEnvErrL_Out(env, RType.ExistError);
  }
}

/**
 * Steps
 * 1. check itself.If true, emit its req
 * 2. If unknown, check its req; if true this time, emit itself
 */
function callDefExec(env: L_Env, node: CallOptNode, relT: DefNode): RL_Out {
  try {
    if (env.checkEmit(node, true)) {
      return cL_Out(RType.True);
    } else {
      const out = relT.checkReq(env, node);
      if (out.v === RType.True) relT.emitTOnlyIf(env, node);
      return out;
    }
  } catch (error) {
    return cEnvErrL_Out(env, RType.DefError);
  }
}

function proveExec(env: L_Env, node: ProveNode): RL_Out {
  try {
    const relatedT = env.getRelT(node.opt.optName);
    switch (relatedT?.type) {
      case L_NodeType.InferNode:
        return proveInferExec(env, node, relatedT);
      case L_NodeType.DefNode:
        return proveDefExec(env, node, relatedT);
    }

    return cEnvErrL_Out(
      env,
      RType.ProveError,
      `prove keyword should be followed by declared template name`
    );
  } catch (error) {
    return cEnvErrL_Out(env, RType.ProveError);
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
function proveInferExec(env: L_Env, node: ProveNode, relT: TNode): RL_Out {
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
        if (isNull(out.v))
          return cL_Out(RType.Unknown, `${req.toString()} unsatisfied.`);
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
    if (isNull(fixedOpts)) return cEnvErrL_Out(env, RType.Error, err);
    for (const req of fixedOpts) {
      if (req.optParams.every((ls) => ls.every((s) => s.startsWith("#")))) {
        const out = env.checkEmit(req, false);
        if (isNull(out.v))
          return cL_Out(RType.Unknown, `${req.toString()} unsatisfied.`);
      } else {
        newEnv.newFactEmit(req, false);
      }
    }

    // Run proveBlock
    for (const expr of node.proveBlock) {
      const out = nodeExec(newEnv, expr);
      if (isNull(out.v)) return out;
    }

    // check and emit onlyIF of opt
    for (const onlyIf of node.opt.onlyIFs) {
      if (newEnv.checkEmit(onlyIf, true, env).v) continue;
      else {
        return cL_Out(RType.Unknown, `${onlyIf.toString()} unknown.`);
      }
    }

    // check and emit onlyIf of relT
    let tmp = fixOpt(
      env,
      node.opt,
      relT.allVars(),
      relT.onlyIfs as CallOptNode[]
    );
    if (isNull(tmp.v)) return cEnvErrL_Out(env, RType.Error, tmp.err);
    for (const onlyIf of tmp.v) {
      if (newEnv.checkEmit(onlyIf, true, env)) continue;
      else {
        return cL_Out(RType.Unknown, `${onlyIf.toString()} unknown.`);
      }
    }

    // emit prove.opt itself, notice how opt of proveNode is literally the same as the fact emitted
    knowCallOptExec(env, node.opt);

    if (node.name !== "") env.newBy(node.name, node.opt);

    return cL_Out(RType.ProveTrue, `${node.opt.toString()}`);
  } catch (error) {
    return cEnvErrL_Out(env, RType.ProveError);
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
function proveDefExec(env: L_Env, node: ProveNode, relT: TNode): RL_Out {
  try {
    const newEnv = new L_Env(env);

    if (
      !node.opt.optParams
        .flat()
        .every((e) => (e.startsWith("#") ? true : env.declaredVars.includes(e)))
    ) {
      const vars = node.opt.optParams.map((ls) => ls.join(",")).join(",");
      return cEnvErrL_Out(
        env,
        RType.ProveError,
        `Some of [${vars}] undeclared.`
      );
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
        if (isNull(out.v))
          return cL_Out(RType.Unknown, `${req.toString()} unsatisfied.`);
      } else {
        newEnv.newFactEmit(req, false);
      }
    }

    // Run proveBlock
    for (const expr of node.proveBlock) {
      const out = nodeExec(newEnv, expr);
      if (isNull(out.v)) return out;
    }

    // Check requirements from relT
    let { v: fixedOpts, err } = fixOpt(
      env,
      proveNoHashParams,
      relT.allVars(),
      relT.allReq()
    );
    if (isNull(fixedOpts)) return cEnvErrL_Out(env, RType.Error, err);
    for (const req of fixedOpts) {
      const out = newEnv.checkEmit(req, false);
      if (isNull(out.v)) return cL_Out(RType.ProveError, out.err);
      if (out.v === false)
        return cL_Out(RType.Unknown, `${req.toString()} unsatisfied.`);
    }

    // check and emit onlyIF of opt
    for (const onlyIf of node.opt.onlyIFs) {
      if (newEnv.checkEmit(onlyIf, true, env)) continue;
      else {
        return cL_Out(RType.Unknown, `${onlyIf.toString()} unknown.`);
      }
    }

    // check and emit onlyIf of relT
    let tmp = fixOpt(
      env,
      node.opt,
      relT.allVars(),
      relT.onlyIfs as CallOptNode[]
    );
    if (isNull(tmp.v)) return cEnvErrL_Out(env, RType.Error, tmp.err);
    for (const onlyIf of tmp.v) {
      if (newEnv.checkEmit(onlyIf, true, env)) continue;
      else {
        return cL_Out(RType.Unknown, `${onlyIf.toString()} unknown.`);
      }
    }

    // emit prove, notice how opt of proveNode is literally the same as the fact emitted
    knowCallOptExec(env, node.opt);

    if (node.name !== "") env.newBy(node.name, node.opt);

    return cL_Out(RType.ProveTrue, `${node.opt.toString()}`);
  } catch (error) {
    return cEnvErrL_Out(env, RType.ProveError);
  }
}
