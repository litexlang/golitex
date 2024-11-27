import {
  ByNode,
  DefNode,
  HaveNode,
  IfNode,
  KnowNode,
  L_Node,
  LetNode,
  LocalEnvNode,
  MacroNode,
  // PostfixProve,
  OptNode,
  PostfixProve,
  ProveNode,
  ReturnNode,
  SpecialNode,
  ToCheckNode,
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

export enum L_Out {
  Error,
  True,
  False,
  Unknown,
}

export const RTypeMap: { [key in L_Out]: string } = {
  [L_Out.Error]: "error",
  [L_Out.False]: "check: false",
  [L_Out.True]: "check: true",
  [L_Out.Unknown]: "check: unknown",
};

export function nodeExec(env: L_Env, node: L_Node, showMsg = true): L_Out {
  try {
    const nodeType = node.constructor.name;

    switch (nodeType) {
      case "IffDefNode":
      case "IfDefNode":
      case "ExistDefNode":
      case "OnlyIfDefNode":
        return defExec(env, node as DefNode);

      case "KnowNode":
        return knowExec(env, node as KnowNode);

      case "LetNode":
        return letExec(env, node as LetNode);

      case "ProveNode":
        return proveExec(env, node as ProveNode);

      case "HaveNode":
        return haveExec(env, node as HaveNode);

      case "PostfixProve":
        return postfixProveExec(env, node as PostfixProve);

      case "LocalEnvNode":
        return localEnvExec(env, node as LocalEnvNode);

      case "ReturnNode":
        return returnExec(env, node as ReturnNode);

      case "SpecialNode":
        return specialExec(env, node as SpecialNode);

      case "UseNode":
        return useExec(env, node as ByNode);

      case "MacroNode":
        return macroExec(env, node as MacroNode);

      default:
        if (node instanceof ToCheckNode) {
          try {
            const out = factExec(env, node as ToCheckNode);

            if (out === L_Out.True) {
              if (showMsg) env.newMessage(`OK! ${node}`);
            } else if (out === L_Out.Unknown) {
              env.newMessage(`Unknown ${node}`);
            } else if (out === L_Out.Error) {
              env.newMessage(`Error ${node}`);
            } else if (out === L_Out.False) {
              env.newMessage(`False ${node}`);
            }

            return out;
          } catch {
            throw Error(`${node as ToCheckNode}`);
          }
        }

        return L_Out.Error;
    }
  } catch (error) {
    if (error instanceof Error) env.newMessage(`Error: ${error.message}`);
    return L_Out.Error;
  }
}

function letExec(env: L_Env, node: LetNode): L_Out {
  try {
    // examine whether some vars are already declared. if not, declare them.
    for (const e of node.vars) {
      const ok = env.newVar(e);
      if (!ok) return L_Out.Error;
      else {
        if (DEBUG_DICT["let"]) {
          env.newMessage(`[new var] ${node.vars}`);
        }
      }
    }

    // examine whether all operators are declared
    for (const f of node.facts) {
      const ok = f.factsDeclared(env);
      if (!ok) {
        env.newMessage(`Not all of facts in ${f} are declared`);
        return L_Out.Error;
      }
    }

    // bind properties given by macro
    for (const e of node.vars) {
      for (const macro of env.getMacros([])) {
        if (macro.testRegex(e)) {
          const map = new Map<string, string>();
          map.set(macro.varName, e);
          const facts = macro.facts.map((e) => e.useMapToCopy(map));
          facts.forEach((e) => L_Memory.store(env, e, [], true, true));
        }
      }
    }

    // store new facts
    for (const onlyIf of node.facts) {
      const ok = L_Memory.store(env, onlyIf, [], false);
      if (!ok) return L_Out.Error;
    }

    return L_Out.True;
  } catch {
    return env.errIntoEnvReturnRType(node);
  }
}

export function knowExec(env: L_Env, node: KnowNode): L_Out {
  try {
    // examine whether all facts are declared.
    // ! NEED TO IMPLEMENT EXAMINE ALL VARS ARE DECLARED.
    for (const f of node.facts) {
      const ok = f.factsDeclared(env);
      if (!ok) {
        env.newMessage(`Not all facts in ${f} are declared`);
        return L_Out.Error;
      }
    }

    // store new knowns
    for (const onlyIf of node.facts) {
      const ok = L_Memory.store(env, onlyIf, [], false);
      if (!ok) return L_Out.Error;
    }

    return L_Out.True;
  } catch {
    return env.errIntoEnvReturnRType(node);
  }
}

function defExec(env: L_Env, node: DefNode): L_Out {
  try {
    // declare new opt
    const ok = L_Memory.declNewFact(env, node);
    if (!ok) {
      env.newMessage(`Failed to store ${node}`);
      return L_Out.Error;
    }

    if (DEBUG_DICT["def"]) {
      const decl = env.getDef(node.name);
      if (!decl) return L_Out.Error;
    }

    return L_Out.True;
  } catch {
    return env.errIntoEnvReturnRType(node);
  }
}

function factExec(env: L_Env, toCheck: ToCheckNode): L_Out {
  try {
    if (!(toCheck.varsDeclared(env, []) && toCheck.factsDeclared(env))) {
      return L_Out.Error;
    }

    const out = L_Checker.check(env, toCheck);
    if (out === L_Out.True) {
      // Store Fact
      const ok = L_Memory.executorStoreFact(env, toCheck, true);
      if (!ok) {
        env.newMessage(`Failed to store ${toCheck}`);
        return L_Out.Error;
      }
    }

    return out;
  } catch {
    env.newMessage(`failed to check ${toCheck}`);
    return L_Out.Error;
  }
}

function localEnvExec(env: L_Env, localEnvNode: LocalEnvNode): L_Out {
  try {
    const newEnv = new L_Env(env);
    for (let i = 0; i < localEnvNode.nodes.length; i++) {
      const out = nodeExec(newEnv, localEnvNode.nodes[i]);
      newEnv.getMessages().forEach((e) => env.newMessage(e));
      newEnv.clearMessages();
      if (L_Out.Error === out) return L_Out.Error;
    }

    return L_Out.True;
  } catch {
    env.newMessage("{}");
    return L_Out.Error;
  }
}

function returnExec(env: L_Env, node: ReturnNode): L_Out {
  try {
    for (const f of node.facts) {
      noVarsOrOptDeclaredHere(env, env, f);
    }

    for (const toProve of node.facts) {
      const out = L_Checker.check(env, toProve);
      if (out !== L_Out.True) return out;
    }

    const storeTo = env.getParent();
    if (storeTo) {
      for (const toProve of node.facts) {
        const ok = L_Memory.store(storeTo, toProve, [], true);
        if (!ok) {
          env.newMessage(`Failed to store ${toProve}`);
          return L_Out.Error;
        }
      }
    }
    return L_Out.True;
  } catch {
    env.newMessage("return");
    return L_Out.Error;
  }
}

function haveExec(env: L_Env, node: HaveNode): L_Out {
  try {
    const exist = env.getDeclExist(node.opt.name);
    if (exist === undefined) {
      env.newMessage(`${node.opt.name} is not exist-type fact.`);
      return L_Out.Error;
    }

    const out = L_Checker.check(env, node.opt);
    if (out !== L_Out.True) {
      env.newMessage(`${node} failed.`);
      return out;
    }

    const facts = exist.instantiate(env, node.opt.vars, node.vars);
    if (facts === undefined) {
      return L_Out.Error;
    }
    node.vars.forEach((e) => env.newVar(e));
    facts.forEach((e) => L_Memory.store(env, e, [], true));

    return L_Out.True;
  } catch {
    env.newMessage("have");
    return L_Out.Error;
  }
}

function specialExec(env: L_Env, node: SpecialNode): L_Out {
  try {
    switch (node.keyword) {
      case ClearKeyword:
        env.clear();
        return L_Out.True;
      case RunKeyword: {
        runFile(env, node.extra as string, true, false);
        return L_Out.True;
      }
    }

    return L_Out.Error;
  } catch {
    env.newMessage(`${node.keyword}`);
    return L_Out.Error;
  }
}

function useExec(env: L_Env, node: ByNode): L_Out {
  try {
    const reqSpace = env.getReqSpace(node.reqSpaceName);
    if (reqSpace === undefined) {
      return env.errIntoEnvReturnRType(`${node.reqSpaceName} undefined.`);
    }

    const map = makeStrStrMap(env, reqSpace.ifVars, node.vars);
    if (map === undefined) {
      return env.errIntoEnvReturnRType(`Failed to call ${node.reqSpaceName}`);
    }

    const req = reqSpace.ifReq.map((e) => e.useMapToCopy(map));
    const onlyIf = reqSpace.onlyIf.map((e) => e.useMapToCopy(map));

    for (const r of req) {
      const out = L_Checker.check(env, r);
      if (out !== L_Out.True) return out;
    }

    for (const f of onlyIf) {
      const ok = L_Memory.store(env, f, [], true, false);
      if (!ok) return L_Out.Error;
    }

    return L_Out.True;
  } catch {
    env.newMessage(`Failed: ${node}`);
    return L_Out.Error;
  }
}

function makeStrStrMap(
  env: L_Env,
  keyVars: string[],
  valueVars: string[],
): Map<string, string> | undefined {
  if (keyVars.length !== valueVars.length) {
    env.newMessage(
      `Require ${keyVars.length} elements, get ${valueVars.length}`,
    );
    return undefined;
  }

  const out = new Map<string, string>();
  for (let i = 0; i < keyVars.length; i++) {
    out.set(keyVars[i], valueVars[i]);
  }

  return out;
}

function macroExec(env: L_Env, node: MacroNode): L_Out {
  try {
    env.newMacro(node);
    return L_Out.True;
  } catch {
    return env.errIntoEnvReturnRType(`Failed: macro ${node}`);
  }
}

function proveExec(env: L_Env, node: ProveNode): L_Out {
  let out = L_Out.Error;
  if (node.contradict === undefined) {
    if (node.toProve !== null) {
      if (node.toProve instanceof IfNode) {
        out = proveIfThen(env, node.toProve, node.block);
      }
    } else {
      out = proveOpt(env, node.fixedIfThenOpt as OptNode, node.block);
    }

    if (out !== L_Out.True) {
      env.newMessage(`Failed: ${node}`);
    }

    return L_Out.Error;
  } else {
    if (node.toProve !== null) {
      env.newMessage(
        `At current version, you can not prove if-then by contradiction.`,
      );
      return L_Out.Error;
    } else {
      return proveOptByContradict(
        env,
        node.fixedIfThenOpt as OptNode,
        node.block,
        node.contradict as OptNode,
      );
    }
  }
}

function proveIfThen(env: L_Env, toProve: IfNode, block: L_Node[]): L_Out {
  try {
    const newEnv = new L_Env(env);
    for (const v of toProve.vars) {
      const ok = newEnv.newVar(v);
      if (!ok) throw Error();
    }

    for (const fact of toProve.req) {
      const ok = L_Memory.store(newEnv, fact, [], true);
      if (!ok) throw Error();
    }

    for (const subNode of block) {
      const out = nodeExec(newEnv, subNode, false);
      if (out === L_Out.Error) {
        newEnv.getMessages().forEach((e) => env.newMessage(e));
        env.newMessage(`Errors: Failed to execute ${subNode}`);
        return L_Out.Error;
      }
    }

    const ok = noVarsOrOptDeclaredHere(env, newEnv, toProve);
    if (!ok) return L_Out.Error;

    for (const toCheck of toProve.onlyIfs) {
      const out = nodeExec(newEnv, toCheck, false);
      if (out !== L_Out.True) return out;
    }

    L_Memory.store(env, toProve, [], true);

    newEnv.getMessages().forEach((e) => env.newMessage(`[prove] ${e}`));

    return L_Out.True;
  } catch {
    env.newMessage(`Error: ${toProve}`);
    return L_Out.Error;
  }
}

function execResult(out: L_Out, node: L_Node): string {
  if (out === L_Out.True) {
    return `OK! ${node}`;
  } else if (out === L_Out.Unknown) {
    return `Unknown ${node}`;
  } else if (out === L_Out.Error) {
    return `Error ${node}`;
  } else if (out === L_Out.False) {
    return `False ${node}`;
  }

  return `???`;
}

function proveOpt(env: L_Env, toProve: OptNode, block: L_Node[]): L_Out {
  try {
    const newEnv = new L_Env(env);

    for (const subNode of block) {
      const out = nodeExec(newEnv, subNode, false);
      env.newMessage(execResult(out, toProve));
      if (out === L_Out.Error) {
        newEnv.getMessages().forEach((e) => env.newMessage(e));
        env.newMessage(`Errors: Failed to execute ${subNode}`);
        return L_Out.Error;
      }
    }

    const ok = noVarsOrOptDeclaredHere(env, newEnv, toProve);
    if (!ok) return L_Out.Error;

    const out = L_Checker.check(newEnv, toProve);
    if (out !== L_Out.True) return out;

    L_Memory.store(env, toProve, [], true);

    newEnv.getMessages().forEach((e) => env.newMessage(`[prove] ${e}`));

    return L_Out.True;
  } catch {
    env.newMessage(`${toProve}`);
    return L_Out.Error;
  }
}

function proveOptByContradict(
  env: L_Env,
  toProve: OptNode,
  block: L_Node[],
  contradict: OptNode,
): L_Out {
  try {
    const newEnv = new L_Env(env);

    toProve.isT = !toProve.isT;
    let ok = L_Memory.store(newEnv, toProve, [], true);
    if (!ok) {
      newEnv.newMessage(`Failed to store ${toProve}`);
      return L_Out.Error;
    }

    for (const subNode of block) {
      const out = nodeExec(newEnv, subNode, false);
      if (out === L_Out.Error) {
        newEnv.getMessages().forEach((e) => env.newMessage(e));
        env.newMessage(`Errors: Failed to execute ${subNode}`);
        return L_Out.Error;
      }
    }

    let out = L_Checker.check(newEnv, contradict);
    if (out !== L_Out.True) {
      env.newMessage(`Errors: Failed to execute ${contradict}`);
      return L_Out.Error;
    }

    contradict.isT = !contradict.isT;
    out = L_Checker.check(newEnv, contradict);
    if (out !== L_Out.True) {
      env.newMessage(`Errors: Failed to execute ${contradict}`);
      return L_Out.Error;
    }

    ok = noVarsOrOptDeclaredHere(env, newEnv, toProve);
    if (!ok) return L_Out.Error;

    toProve.isT = !toProve.isT;
    ok = L_Memory.store(env, toProve, [], true);
    if (!ok) {
      env.newMessage(`Failed to store ${toProve}`);
      return L_Out.Error;
    }

    newEnv.getMessages().forEach((e) =>
      env.newMessage(`[prove_by_contradict] ${e}`)
    );

    return L_Out.True;
  } catch {
    env.newMessage(`${toProve}`);
    return L_Out.Error;
  }
}

function postfixProveExec(env: L_Env, PostfixProve: PostfixProve): L_Out {
  try {
    const newEnv = new L_Env(env);
    for (const subNode of PostfixProve.block) {
      const out = nodeExec(newEnv, subNode, false);
      if (out !== L_Out.True) {
        newEnv.getMessages().forEach((e) => env.newMessage(e));
        env.newMessage(`${PostfixProve} failed.`);
        return out;
      }
    }

    for (const fact of PostfixProve.facts) {
      const ok = noVarsOrOptDeclaredHere(env, newEnv, fact);
      if (!ok) return L_Out.Error;
    }

    for (const fact of PostfixProve.facts) {
      const out = L_Checker.check(newEnv, fact);
      if (out !== L_Out.True) {
        newEnv.getMessages().forEach((e) => env.newMessage(e));
        env.newMessage(`${PostfixProve} failed.`);
        return out;
      }
    }

    for (const fact of PostfixProve.facts) {
      const ok = L_Memory.store(env, fact, [], true);
      if (!ok) {
        env.newMessage(`Failed to store ${fact}`);
        return L_Out.Error;
      }
    }

    newEnv.getMessages().forEach((e) => env.newMessage(`[prove] ${e}`));

    return L_Out.True;
  } catch {
    env.newMessage("by error");
    return L_Out.Error;
  }
}

//
function noVarsOrOptDeclaredHere(
  sendErrMessageToEnv: L_Env,
  here: L_Env,
  targetFact: ToCheckNode,
): boolean {
  if (here.someVarsDeclaredHere(targetFact, [])) {
    here.getMessages().forEach((e) => sendErrMessageToEnv.newMessage(e));
    sendErrMessageToEnv.newMessage(
      `Error: Some variables in ${targetFact} are declared in block. It's illegal to declare operator or variable with the same name in the if-then expression you want to prove.`,
    );
    return false;
  }

  if (here.someOptsDeclaredHere(targetFact)) {
    here.getMessages().forEach((e) => sendErrMessageToEnv.newMessage(e));
    sendErrMessageToEnv.newMessage(
      `Error: Some operators in ${targetFact} are declared in block. It's illegal to declare operator or variable with the same name in the if-then expression you want to prove.`,
    );
    return false;
  }

  return true;
}
