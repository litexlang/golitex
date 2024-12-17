import { L_Env } from "./L_Env";
import * as L_Checker from "./L_Checker";
import * as L_Memory from "./L_Memory";
import { L_Keywords } from "./L_Keywords";
import { runFile } from "./L_Runner";
import * as L_Nodes from "./L_Nodes";
import * as L_Messages from "./L_Messages";
import { L_Out, L_Singleton } from "./L_Structs";
import { optsVarsDeclaredInFacts } from "./L_ExecutorHelper";

export const DEBUG_DICT = {
  newFact: true,
  def: true,
  check: true,
  storeBy: true,
  let: true,
  checkCompositeVar: true,
};

export const CheckFalse = true;

export const L_OutMap: { [key in L_Out]: string } = {
  [L_Out.Error]: "error",
  [L_Out.False]: "check: false",
  [L_Out.True]: "check: true",
  [L_Out.Unknown]: "check: unknown",
};

export function L_Exec(env: L_Env, node: L_Nodes.L_Node): L_Out {
  try {
    const nodeType = node.constructor.name;

    switch (nodeType) {
      case "DefNode":
        return defExec(env, node as L_Nodes.DefNode);
      case "KnowNode":
        return knowExec(env, node as L_Nodes.KnowNode);
      case "DefCompositeNode":
        return defCompositeExec(env, node as L_Nodes.DefCompositeNode);
      case "LetNode":
        return letExec(env, node as L_Nodes.LetNode);
      case "ProveNode":
        return proveExec(env, node as L_Nodes.ProveNode);
      case "ProveContradictNode":
        return proveContradictExec(env, node as L_Nodes.ProveContradictNode);
      case "LocalEnvNode":
        return localEnvExec(env, node as L_Nodes.LocalEnvNode);
      case "SpecialNode":
        return specialExec(env, node as L_Nodes.SpecialNode);
      case "MacroNode":
        return macroExec(env, node as L_Nodes.MacroNode);
      default:
        if (node instanceof L_Nodes.ToCheckNode) {
          const out = factExec(env, node as L_Nodes.ToCheckNode);
          env.report(L_Messages.reportExecL_Out(out, node));
          return out;
        }

        return L_Out.Error;
    }
  } catch (error) {
    return L_Messages.L_ReportErr(env, L_Exec, node);
  }
}

function letExec(env: L_Env, node: L_Nodes.LetNode): L_Out {
  try {
    // examine whether some vars are already declared. if not, declare them.
    for (const e of node.vars) {
      const ok = env.newSingletonVar(e);
      if (!ok) return L_Out.Error;
    }

    if (!optsVarsDeclaredInFacts(env, [])) {
      throw Error();
    }

    // TODO bind macro

    // store new facts
    for (const onlyIf of node.facts) {
      const ok = L_Memory.newFact(env, onlyIf);
      if (!ok) {
        L_Messages.reportStoreErr(env, knowExec.name, onlyIf);
        throw new Error();
      }
    }

    return L_Out.True;
  } catch {
    return L_Messages.L_ReportErr(env, letExec, node);
  }
}

export function knowExec(env: L_Env, node: L_Nodes.KnowNode): L_Out {
  try {
    // examine whether all facts are declared.
    // ! NEED TO IMPLEMENT EXAMINE ALL VARS ARE DECLARED.
    if (!optsVarsDeclaredInFacts(env, node.facts)) {
      throw Error();
    }

    // store new knowns
    for (const onlyIf of node.facts) {
      const ok = L_Memory.newFact(env, onlyIf);
      if (!ok) {
        L_Messages.reportStoreErr(env, knowExec.name, onlyIf);
        throw new Error();
      }
    }

    // for (const [i, v] of node.names.entries()) {
    //   const ok = env.newNamedKnownToCheck(v, node.facts[i]);
    //   if (!ok) throw new Error();
    // }

    return L_Out.True;
  } catch {
    return L_Messages.L_ReportErr(env, knowExec, node);
  }
}

function defExec(env: L_Env, node: L_Nodes.DefNode): L_Out {
  try {
    // declare new opt
    const ok = L_Memory.declNewFact(env, node);
    if (!ok) {
      env.report(`Failed to store ${node}`);
      return L_Out.Error;
    }

    if (!optsVarsDeclaredInFacts(env, node.onlyIfs)) {
      throw Error();
    }

    return L_Out.True;
  } catch {
    return L_Messages.L_ReportErr(env, defExec, node);
  }
}

function factExec(env: L_Env, toCheck: L_Nodes.ToCheckNode): L_Out {
  try {
    // TODO: Implement check whether the given toCheck exists and given var exists.

    const out = L_Checker.checkFact(env, toCheck);

    if (out === L_Out.True) {
      // Store Fact
      const ok = L_Memory.newFact(env, toCheck);
      if (!ok) {
        env.report(`Failed to store ${toCheck}`);
        return L_Out.Error;
      }
    }

    return out;
  } catch {
    return L_Messages.L_ReportErr(env, factExec, toCheck);
  }
}

function localEnvExec(env: L_Env, localEnvNode: L_Nodes.LocalEnvNode): L_Out {
  try {
    const newEnv = new L_Env(env);
    env.report(`[local environment]\n`);
    for (let i = 0; i < localEnvNode.nodes.length; i++) {
      const out = L_Exec(newEnv, localEnvNode.nodes[i]);
      newEnv.getMessages().forEach((e) => env.report(e));
      newEnv.clearMessages();
      if (L_Out.Error === out) return L_Out.Error;
    }
    env.report(`\n[end of local environment]`);

    return L_Out.True;
  } catch {
    return L_Messages.L_ReportErr(env, localEnvExec, localEnvExec);
  }
}

function specialExec(env: L_Env, node: L_Nodes.SpecialNode): L_Out {
  try {
    switch (node.keyword) {
      case L_Keywords.ClearKeyword:
        env.clear();
        return L_Out.True;
      case L_Keywords.RunKeyword: {
        runFile(env, node.extra as string, true, false);
        return L_Out.True;
      }
    }

    return L_Out.Error;
  } catch {
    return L_Messages.L_ReportErr(env, specialExec, node);
  }
}

function macroExec(env: L_Env, node: L_Nodes.MacroNode): L_Out {
  try {
    env.newMacro(node);
    return L_Out.True;
  } catch {
    return L_Messages.L_ReportErr(env, macroExec, node);
  }
}

function proveContradictExec(
  env: L_Env,
  proveNode: L_Nodes.ProveContradictNode
): L_Out {
  try {
    const newEnv = new L_Env(env);
    const negativeToProve = proveNode.toProve.copyWithIsTReverse();
    L_Memory.newFact(newEnv, negativeToProve);

    // TODO Must check all opt and vars in toProve is declared in env instead of in env
    for (const node of proveNode.block) {
      const out = L_Exec(newEnv, node);
      if (out !== L_Out.True) {
        env.report(`failed to run ${node}`);
        throw Error();
      }
    }

    const out = factExec(newEnv, proveNode.contradict);
    const out2 = factExec(newEnv, proveNode.contradict.copyWithIsTReverse());

    if (out === L_Out.True && out2 === L_Out.True) {
      L_Memory.newFact(env, proveNode.toProve);
      env.report(`[prove_by_contradict] ${proveNode.toProve}`);
      return L_Out.True;
    } else {
      env.report(
        `failed: ${proveNode.contradict} is supposed to be both true and false`
      );
      return L_Out.Unknown;
    }
  } catch {
    return L_Messages.L_ReportErr(env, proveContradictExec, proveNode);
  }
}

function proveExec(env: L_Env, proveNode: L_Nodes.ProveNode): L_Out {
  try {
    const newEnv = new L_Env(env);
    if (proveNode.toProve instanceof L_Nodes.IfNode) {
      return proveIfExec(env, proveNode);
    } else if (proveNode.toProve instanceof L_Nodes.OptNode) {
      return proveOptExec(env, proveNode);
    }

    throw Error();
  } catch {
    return L_Messages.L_ReportErr(env, proveExec, proveNode);
  }
}

function proveOptExec(env: L_Env, proveNode: L_Nodes.ProveNode): L_Out {
  try {
    const newEnv = new L_Env(env);

    // TODO Must check all opt and vars in toProve is declared in env instead of in env
    for (const node of proveNode.block) {
      const out = L_Exec(newEnv, node);
      if (out !== L_Out.True) {
        env.report(`failed to run ${node}`);
        throw Error();
      }
    }

    const out = L_Checker.checkFact(newEnv, proveNode.toProve);
    if (out === L_Out.True) {
      const ok = L_Memory.newFact(env, proveNode.toProve);
      if (ok) return L_Out.True;
      else throw Error();
    } else {
      env.report(`[prove failed] ${proveNode.toProve}`);
      return L_Out.Unknown;
    }
  } catch {
    return L_Messages.L_ReportErr(env, proveOptExec, proveNode);
  }
}

function proveIfExec(env: L_Env, proveNode: L_Nodes.ProveNode): L_Out {
  try {
    const newEnv = new L_Env(env);
    const toProve = proveNode.toProve as L_Nodes.IfNode;

    let ok = true;
    for (const v of toProve.vars) {
      //TODO how to composite?
      if (v instanceof L_Singleton) {
        ok = env.newSingletonVar(v.value);
        if (!ok) {
          env.report(`Failed: ${v} already declared`);
          throw Error();
        }
      }
    }

    for (const node of toProve.req) {
      ok = L_Memory.newFact(newEnv, node);
      if (!ok) {
        throw Error();
      }
    }

    // TODO Must check all opt and vars in toProve is declared in env instead of in env
    for (const node of proveNode.block) {
      const out = L_Exec(newEnv, node);
      if (out !== L_Out.True) {
        env.report(`failed to run ${node}`);
        throw Error();
      }
    }

    for (const onlyIf of toProve.onlyIfs) {
      const out = factExec(newEnv, onlyIf);
      if (out !== L_Out.True) {
        env.report(`Failed to check ${onlyIf}`);
        throw Error();
      }
    }

    const out = L_Memory.newFact(env, toProve);
    if (out) {
      env.report(`[prove] ${proveNode}`);
      return L_Out.True;
    } else {
      throw Error();
    }
  } catch {
    return L_Messages.L_ReportErr(env, proveIfExec, proveNode);
  }
}

function defCompositeExec(env: L_Env, node: L_Nodes.DefCompositeNode): L_Out {
  try {
    if (env.newCompositeVar(node.composite.name, node)) {
      env.report(`OK! ${node}`);
      return L_Out.True;
    } else {
      throw Error();
    }
  } catch {
    return L_Messages.L_ReportErr(env, defCompositeExec, node);
  }
}
