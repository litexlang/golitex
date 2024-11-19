import {
  KnowNode,
  L_Node,
  LetNode,
  ToCheckNode,
  DefNode,
  ProveNode,
  // HaveNode,
  PostfixProve,
  OptNode,
  LocalEnvNode,
  ReturnNode,
  // ReturnExistNode,
  // ByNode,
  IfNode,
  HaveNode,
  SpecialNode,
  CallNode,
  // STNode,
} from "./L_Nodes.ts";
import { L_Env } from "./L_Env.ts";
import * as L_Checker from "./L_Checker.ts";
import * as L_Memory from "./L_Memory.ts";
import { ClearKeyword, RunKeyword } from "./L_Common.ts";
import { runFile } from "./L_Runner.ts";

export const DEBUG_DICT = {
  newFact: true,
  def: true,
  check: true,
  storeBy: true,
  let: true,
};

export const CheckFalse = true;

export enum RType {
  Error,
  True,
  False,
  Unknown,
}

export const RTypeMap: { [key in RType]: string } = {
  [RType.Error]: "error",
  [RType.False]: "check: false",
  [RType.True]: "check: true",
  [RType.Unknown]: "check: unknown",
};

function successMesIntoEnv(env: L_Env, node: L_Node): RType {
  env.newMessage(`OK! ${node.toString()}`);
  return RType.True;
}

function errIntoEnv(env: L_Env, s: string): RType {
  env.newMessage(`Error: ${s}`);
  return RType.Error;
}

// deno-lint-ignore no-explicit-any
const nodeExecMap: { [key: string]: (env: L_Env, node: any) => RType } = {
  IffDefNode: defExec,
  IfDefNode: defExec,
  ExistDefNode: defExec,
  OnlyIfDefNode: defExec,
  KnowNode: knowExec,
  LetNode: letExec,
  ProveNode: proveExec,
  HaveNode: haveExec,
  PostfixProve: postfixProveExec,
  LocalEnvNode: localEnvExec,
  ReturnNode: returnExec,
  SpecialNode: specialExec,
  CallNode: callExec,
  // ReturnExistNode: returnExistExec,
  // ByNode: byExec,
  // STNode: byExec,
};

function execResult(out: RType, node: L_Node): string {
  if (out === RType.True) {
    return `OK! ${node}`;
  } else if (out === RType.Unknown) {
    return `Unknown ${node}`;
  } else if (out === RType.Error) {
    return `Error ${node}`;
  }

  return `???`;
}

export function nodeExec(env: L_Env, node: L_Node, showMsg = true): RType {
  try {
    const nodeType = node.constructor.name;

    const execFunc = nodeExecMap[nodeType];

    if (execFunc) {
      const out = execFunc(env, node);
      if (out === RType.True) return successMesIntoEnv(env, node);
    } else if (node instanceof ToCheckNode) {
      try {
        const out = factExec(env, node as ToCheckNode);

        if (out === RType.True && showMsg) {
          env.newMessage(`OK! ${node}`);
        } else if (out === RType.Unknown) {
          env.newMessage(`Unknown ${node}`);
        } else if (out === RType.Error) {
          env.newMessage(`Error ${node}`);
        } else if (out === RType.False) {
          env.newMessage(`False ${node}`);
        }
        return out;
      } catch {
        throw Error(`${node as ToCheckNode}`);
      }
    }
    return RType.Error;
  } catch (error) {
    if (error instanceof Error) env.newMessage(`Error: ${error.message}`);
    return RType.Error;
  }
}

// function haveExec(env: L_Env, node: HaveNode): RType {
//   try {
//     for (const e of node.vars) {
//       const ok = env.safeNewVar(e);
//       if (!ok) return RType.Error;
//     }

//     for (const f of node.facts) {
//       const ok = f.factsDeclared(env);
//       if (!ok) {
//         env.newMessage(`Not all of operators in ${f} are declared`);
//         return RType.Error;
//       }
//     }

//     for (const fact of node.facts) {
//       if (!env.inHaves(fact.name)) {
//         env.newMessage(`Not every existence of given fact is validated.`);
//         return RType.Error;
//       }
//     }

//     for (const fact of node.facts) {
//       if (node.vars.every((e) => !fact.vars.includes(e))) {
//         env.newMessage(`${fact} does not include any newly declared variable.`);
//         return RType.Error;
//       }
//       const ok = L_Memory.store(env, fact, [], true);
//       if (!ok) {
//         env.newMessage(`Failed to store ${fact}`);
//         return RType.Error;
//       }
//     }

//     return RType.True;
//   } catch {
//     env.newMessage(`Error: ${node.toString()}`);
//     return RType.Error;
//   }
// }

function letExec(env: L_Env, node: LetNode): RType {
  try {
    for (const e of node.vars) {
      const ok = env.safeNewVar(e);
      if (!ok) return RType.Error;
      else {
        if (DEBUG_DICT["let"]) {
          env.newMessage(`[new var] ${node.vars}`);
        }
      }
    }
    // node.vars.forEach((e) => env.newVar(e, e));

    // examine whether all operators are declared
    for (const f of node.facts) {
      const ok = f.factsDeclared(env);
      if (!ok) {
        env.newMessage(`Not all of facts in ${f} are declared`);
        return RType.Error;
      }
    }

    // declare defNames

    // const ok = L_Memory.declDefNames(env, node.facts, true);
    // if (!ok) {
    //   env.newMessage(`Failed to declare new operators in ${node}`);
    //   return RType.Error;
    // }

    // check all requirements are satisfied
    if (!node.strict) {
      // store facts
      for (const f of node.facts) {
        const ok = L_Memory.executorStoreFact(env, f, true);
        if (!ok) {
          env.newMessage(`Failed to store ${f}`);
          return RType.Error;
        }
      }
    }

    return RType.True;
  } catch {
    env.newMessage(`Error: ${node.toString()}`);
    return RType.Error;
  }
}

export function knowExec(env: L_Env, node: KnowNode): RType {
  try {
    for (const f of node.facts) {
      const ok = f.factsDeclared(env);
      if (!ok) {
        env.newMessage(`Not all facts in ${f} are declared`);
        return RType.Error;
      }
    }

    if (!node.strict) {
      for (const fact of node.facts) {
        const ok = L_Memory.executorStoreFact(env, fact, true);
        if (!ok) {
          env.newMessage(`Failed to store ${fact}`);
          return RType.Error;
        }
      }
    }

    // L_Memory.declDefNames(env, node.facts, false);

    return RType.True;
  } catch (error) {
    let m = `'${node.toString()}'`;
    if (error instanceof Error) m += ` ${error.message}`;
    env.newMessage(m);
    throw error;
  }
}

function defExec(env: L_Env, node: DefNode): RType {
  try {
    // let ok = env.safeDeclOpt(node.name, node);
    // if (!ok) return RType.Error;

    // declare new opt
    const ok = L_Memory.declNewFact(env, node);
    if (!ok) {
      env.newMessage(`Failed to store ${node}`);
      return RType.Error;
    }

    // store declared opt by
    // L_Memory.storeDeclaredIfThenAsBy(env, node);

    // for (const onlyIf of node.onlyIfs) {
    //   if (onlyIf instanceof IfNode) {
    //     const higherStoreReq = new StoredReq(node.vars, [
    //       new OptNode(node.name, node.vars, true, undefined),
    //       ...node.req,
    //     ]);
    //     const higherStoredFact = new StoredFact([], [higherStoreReq], true);
    //     L_Memory.storeIfThenBy(env, onlyIf, higherStoredFact);
    //   }
    // }

    if (DEBUG_DICT["def"]) {
      const decl = env.getDeclaredFact(node.name);
      if (!decl) return RType.Error;
    }

    return RType.True;
  } catch (error) {
    let m = `'${node.toString()}'`;
    if (error instanceof Error) m += ` ${error.message}`;
    env.newMessage(m);
    throw error;
  }
}

function proveExec(env: L_Env, node: ProveNode): RType {
  let out = RType.Error;
  if (node.contradict === undefined) {
    if (node.toProve !== null) {
      if (node.toProve instanceof IfNode) {
        out = proveIfThen(env, node.toProve, node.block);
      }
    } else {
      out = proveOpt(env, node.fixedIfThenOpt as OptNode, node.block);
    }

    if (out !== RType.True) {
      env.newMessage(`Failed: ${node}`);
    }

    return RType.Error;
  } else {
    if (node.toProve !== null) {
      env.newMessage(
        `At current version, you can not prove if-then by contradiction.`
      );
      return RType.Error;
    } else {
      return proveOptByContradict(
        env,
        node.fixedIfThenOpt as OptNode,
        node.block,
        node.contradict as OptNode
      );
    }
  }
}

function proveIfThen(env: L_Env, toProve: IfNode, block: L_Node[]): RType {
  try {
    const newEnv = new L_Env(env);
    for (const v of toProve.vars) {
      const ok = newEnv.safeNewVar(v);
      if (!ok) throw Error();
    }

    for (const fact of toProve.req) {
      const ok = L_Memory.store(newEnv, fact, [], true);
      if (!ok) throw Error();
    }

    for (const subNode of block) {
      const out = nodeExec(newEnv, subNode, false);
      if (out === RType.Error) {
        newEnv.getMessages().forEach((e) => env.newMessage(e));
        env.newMessage(`Errors: Failed to execute ${subNode}`);
        return RType.Error;
      }
    }

    if (newEnv.someVarsDeclaredHere(toProve, [])) {
      newEnv.getMessages().forEach((e) => env.newMessage(e));
      env.newMessage(
        `Error: Some variables in ${toProve} are declared in block. It's illegal to declare operator or variable with the same name in the if-then expression you want to prove.`
      );
      return RType.Error;
    }

    if (newEnv.someOptsDeclaredHere(toProve)) {
      newEnv.getMessages().forEach((e) => env.newMessage(e));
      env.newMessage(
        `Error: Some operators in ${toProve} are declared in block. It's illegal to declare operator or variable with the same name in the if-then expression you want to prove.`
      );
      return RType.Error;
    }

    for (const toCheck of toProve.onlyIfs) {
      const out = nodeExec(newEnv, toCheck, false);
      if (out !== RType.True) return out;
    }

    L_Memory.store(env, toProve, [], true);

    newEnv.getMessages().forEach((e) => env.newMessage(e));

    return RType.True;
  } catch {
    env.newMessage(`Error: ${toProve}`);
    return RType.Error;
  }
}

function proveOpt(env: L_Env, toProve: OptNode, block: L_Node[]): RType {
  try {
    const newEnv = new L_Env(env);

    for (const subNode of block) {
      const out = nodeExec(newEnv, subNode, false);
      env.newMessage(execResult(out, toProve));
      if (out === RType.Error) {
        newEnv.getMessages().forEach((e) => env.newMessage(e));
        env.newMessage(`Errors: Failed to execute ${subNode}`);
        return RType.Error;
      }
    }

    if (newEnv.someVarsDeclaredHere(toProve, [])) {
      newEnv.getMessages().forEach((e) => env.newMessage(e));
      env.newMessage(
        `Error: Some variables in ${toProve} are declared in block. It's illegal to declare operator or variable with the same name in the if-then expression you want to prove.`
      );
      return RType.Error;
    }

    if (newEnv.someOptsDeclaredHere(toProve)) {
      newEnv.getMessages().forEach((e) => env.newMessage(e));
      env.newMessage(
        `Error: Some operators in ${toProve} are declared in block. It's illegal to declare operator or variable with the same name in the if-then expression you want to prove.`
      );
      return RType.Error;
    }

    const out = L_Checker.check(newEnv, toProve);
    if (out !== RType.True) return out;

    L_Memory.store(env, toProve, [], true);

    return RType.True;
  } catch {
    env.newMessage(`${toProve}`);
    return RType.Error;
  }
}

function proveOptByContradict(
  env: L_Env,
  toProve: OptNode,
  block: L_Node[],
  contradict: OptNode
): RType {
  try {
    const newEnv = new L_Env(env);

    toProve.isT = !toProve.isT;
    let ok = L_Memory.store(newEnv, toProve, [], true);
    if (!ok) {
      newEnv.newMessage(`Failed to store ${toProve}`);
      return RType.Error;
    }

    for (const subNode of block) {
      const out = nodeExec(newEnv, subNode, false);
      if (out === RType.Error) {
        newEnv.getMessages().forEach((e) => env.newMessage(e));
        env.newMessage(`Errors: Failed to execute ${subNode}`);
        return RType.Error;
      }
    }

    let out = L_Checker.check(newEnv, contradict);
    if (out !== RType.True) {
      env.newMessage(`Errors: Failed to execute ${contradict}`);
      return RType.Error;
    }

    contradict.isT = !contradict.isT;
    out = L_Checker.check(newEnv, contradict);
    if (out !== RType.True) {
      env.newMessage(`Errors: Failed to execute ${contradict}`);
      return RType.Error;
    }

    if (newEnv.someVarsDeclaredHere(toProve, [])) {
      newEnv.getMessages().forEach((e) => env.newMessage(e));
      env.newMessage(
        `Error: Some variables in ${toProve} are declared in block. It's illegal to declare operator or variable with the same name in the if-then expression you want to prove.`
      );
      return RType.Error;
    }

    if (newEnv.someOptsDeclaredHere(toProve)) {
      newEnv.getMessages().forEach((e) => env.newMessage(e));
      env.newMessage(
        `Error: Some operators in ${toProve} are declared in block. It's illegal to declare operator or variable with the same name in the if-then expression you want to prove.`
      );
      return RType.Error;
    }

    toProve.isT = !toProve.isT;
    ok = L_Memory.store(env, toProve, [], true);
    if (!ok) {
      env.newMessage(`Failed to store ${toProve}`);
      return RType.Error;
    }

    newEnv.getMessages().forEach((e) => env.newMessage(e));

    return RType.True;
  } catch {
    env.newMessage(`${toProve}`);
    return RType.Error;
  }
}

function postfixProveExec(env: L_Env, PostfixProve: PostfixProve): RType {
  try {
    const newEnv = new L_Env(env);
    for (const subNode of PostfixProve.block) {
      const out = nodeExec(newEnv, subNode, false);
      if (out !== RType.True) {
        newEnv.getMessages().forEach((e) => env.newMessage(e));
        env.newMessage(`${PostfixProve} failed.`);
        return out;
      }
    }

    for (const fact of PostfixProve.facts) {
      if (newEnv.someVarsDeclaredHere(fact, [])) {
        newEnv.getMessages().forEach((e) => env.newMessage(e));
        env.newMessage(
          `Error: Some variables in ${fact} are declared in block. It's illegal to declare operator or variable with the same name in the if-then expression you want to prove.`
        );
        return RType.Error;
      }

      if (newEnv.someOptsDeclaredHere(fact)) {
        newEnv.getMessages().forEach((e) => env.newMessage(e));
        env.newMessage(
          `Error: Some operators in ${fact} are declared in block. It's illegal to declare operator or variable with the same name in the if-then expression you want to prove.`
        );
        return RType.Error;
      }
    }

    for (const fact of PostfixProve.facts) {
      const out = L_Checker.check(newEnv, fact);
      if (out !== RType.True) {
        newEnv.getMessages().forEach((e) => env.newMessage(e));
        env.newMessage(`${PostfixProve} failed.`);
        return out;
      }
    }

    for (const fact of PostfixProve.facts) {
      const ok = L_Memory.store(env, fact, [], true);
      if (!ok) {
        env.newMessage(`Failed to store ${fact}`);
        return RType.Error;
      }
    }

    newEnv.getMessages().forEach((e) => env.newMessage(e));

    return RType.True;
  } catch {
    env.newMessage("by error");
    return RType.Error;
  }
}

function factExec(env: L_Env, toCheck: ToCheckNode): RType {
  try {
    if (!(toCheck.varsDeclared(env, []) && toCheck.factsDeclared(env))) {
      return RType.Error;
    }

    const out = L_Checker.check(env, toCheck);
    if (out === RType.True) {
      // Store Fact
      const ok = L_Memory.executorStoreFact(env, toCheck, true);
      if (!ok) {
        env.newMessage(`Failed to store ${toCheck}`);
        return RType.Error;
      }
    }

    return out;
  } catch {
    env.newMessage(`failed to check ${toCheck}`);
    return RType.Error;
  }
}

function localEnvExec(env: L_Env, localEnvNode: LocalEnvNode): RType {
  try {
    const newEnv = new L_Env(env);
    for (let i = 0; i < localEnvNode.nodes.length; i++) {
      const out = nodeExec(newEnv, localEnvNode.nodes[i]);
      newEnv.getMessages().forEach((e) => env.newMessage(e));
      newEnv.clearMessages();
      if (RType.Error === out) return RType.Error;
    }

    return RType.True;
  } catch {
    env.newMessage("{}");
    return RType.Error;
  }
}

function returnExec(env: L_Env, node: ReturnNode): RType {
  try {
    for (const f of node.facts) {
      if (env.someOptsDeclaredHere(f)) {
        env.newMessage(
          `Error: Some operators in ${f} are declared in block. It's illegal to declare operator or variable with the same name in the if-then expression you want to prove.`
        );
        return RType.Error;
      }
      if (env.someVarsDeclaredHere(f, [])) {
        env.newMessage(
          `Error: Some variables in ${f} are declared in block. It's illegal to declare operator or variable with the same name in the if-then expression you want to prove.`
        );
        return RType.Error;
      }
    }

    for (const toProve of node.facts) {
      const out = L_Checker.check(env, toProve);
      if (out !== RType.True) return out;
    }

    const storeTo = env.getFather();
    if (storeTo) {
      for (const toProve of node.facts) {
        const ok = L_Memory.store(storeTo, toProve, [], true);
        if (!ok) {
          env.newMessage(`Failed to store ${toProve}`);
          return RType.Error;
        }
      }
    }
    return RType.True;
  } catch {
    env.newMessage("return");
    return RType.Error;
  }
}

function haveExec(env: L_Env, node: HaveNode): RType {
  try {
    const exist = env.getDeclExist(node.opt.name);
    if (exist === undefined) {
      env.newMessage(`${node.opt.name} is not exist-type fact.`);
      return RType.Error;
    }

    const out = L_Checker.check(env, node.opt);
    if (out !== RType.True) {
      env.newMessage(`${node} failed.`);
      return out;
    }

    const facts = exist.instantiate(env, node.opt.vars, node.vars);
    if (facts === undefined) {
      return RType.Error;
    }
    node.vars.forEach((e) => env.safeNewVar(e));
    facts.forEach((e) => L_Memory.store(env, e, [], true));

    return RType.True;
  } catch {
    env.newMessage("have");
    return RType.Error;
  }
}

function specialExec(env: L_Env, node: SpecialNode): RType {
  try {
    switch (node.keyword) {
      case ClearKeyword:
        env.clear();
        return RType.True;
      case RunKeyword: {
        runFile(env, node.extra as string, true, false);
        return RType.True;
      }
    }

    return RType.Error;
  } catch {
    env.newMessage(`${node.keyword}`);
    return RType.Error;
  }
}

function callExec(env: L_Env, node: CallNode): RType {
  try {
    const reqSpace = env.getReqSpace(node.reqSpaceName);
    if (reqSpace === undefined)
      return errIntoEnv(env, `${node.reqSpaceName} undefined.`);

    return RType.True;
  } catch {
    env.newMessage(`Failed: ${node}`);
    return RType.Error;
  }
}
