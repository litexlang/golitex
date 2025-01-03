import { L_Env } from "./L_Env";
import * as L_Checker from "./L_Checker";
import * as L_Memory from "./L_Memory";
import * as L_Nodes from "./L_Nodes";
import * as L_Report from "./L_Report";
import { L_Out, L_Singleton, L_Symbol } from "./L_Structs";

export const DEBUG_DICT = {
  newFact: true,
  def: true,
  check: true,
  storeBy: true,
  let: true,
  checkCompositeVar: true,
};

export const CheckFalse = true;

export function L_Exec(env: L_Env, node: L_Nodes.L_Node): L_Out {
  try {
    if (node instanceof L_Nodes.L_FactNode) {
      return factExec(env, node);
    } else if (node instanceof L_Nodes.ProveNode) {
      return proveExec(env, node);
    } else if (node instanceof L_Nodes.ProveContradictNode) {
      return proveContradictExec(env, node);
    } else if (node instanceof L_Nodes.LocalEnvNode) {
      return localEnvExec(env, node);
    }

    throw new Error(`${node} can not be executed at runtime.`);
  } catch (error) {
    return L_Report.L_ReportErr(env, L_Exec, node, error);
  }
}

function factExec(env: L_Env, toCheck: L_Nodes.L_FactNode): L_Out {
  try {
    // TODO: Implement check whether the given toCheck exists and given var exists.

    const out = L_Checker.checkFact(env, toCheck);

    if (out === L_Out.True) {
      L_Memory.tryNewFact(env, toCheck);
    }

    return L_Report.reportL_Out(env, out, toCheck);
  } catch {
    return L_Report.L_ReportErr(env, factExec, toCheck);
  }
}

function localEnvExec(env: L_Env, localEnvNode: L_Nodes.LocalEnvNode): L_Out {
  try {
    env.report(`[new local environment]\n`);
    let out = L_Out.True;
    for (let i = 0; i < localEnvNode.nodes.length; i++) {
      const ok = L_Exec(localEnvNode.localEnv, localEnvNode.nodes[i]);
      localEnvNode.localEnv.getMessages().forEach((e) => env.report(e));
      localEnvNode.localEnv.clearMessages();
      if (L_Out.True !== ok) {
        out = ok;
        if (L_Out.Error === out) return L_Out.Error;
      }
    }
    env.report(`\n[end of local environment]`);

    return out;
  } catch {
    return L_Report.L_ReportErr(env, localEnvExec, localEnvExec);
  }
}

function proveContradictExec(
  env: L_Env,
  proveNode: L_Nodes.ProveContradictNode
): L_Out {
  try {
    const newEnv = new L_Env(env);
    const negativeToProve = proveNode.toProve.copyWithIsTReverse();
    L_Memory.tryNewFact(newEnv, negativeToProve);

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
      L_Memory.tryNewFact(env, proveNode.toProve);
      env.report(`[prove_by_contradict] ${proveNode.toProve}`);
      return L_Out.True;
    } else {
      env.report(
        `failed: ${proveNode.contradict} is supposed to be both true and false`
      );
      return L_Out.Unknown;
    }
  } catch {
    return L_Report.L_ReportErr(env, proveContradictExec, proveNode);
  }
}

function proveExec(env: L_Env, proveNode: L_Nodes.ProveNode): L_Out {
  try {
    const newEnv = new L_Env(env);
    if (proveNode.toProve instanceof L_Nodes.IfNode) {
      return proveIfExec(env, proveNode);
    } else if (proveNode.toProve instanceof L_Nodes.OptFactNode) {
      return proveOptExec(env, proveNode);
    }

    throw Error();
  } catch {
    return L_Report.L_ReportErr(env, proveExec, proveNode);
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
      L_Memory.tryNewFact(env, proveNode.toProve);
      return L_Out.True;
    } else {
      env.report(`[prove failed] ${proveNode.toProve}`);
      return L_Out.Unknown;
    }
  } catch {
    return L_Report.L_ReportErr(env, proveOptExec, proveNode);
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
        env.tryNewPureSingleton(v.value);
      }
    }

    for (const node of toProve.req) {
      L_Memory.tryNewFact(newEnv, node);
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

    L_Memory.tryNewFact(env, toProve);
    env.report(`[prove] ${proveNode}`);
    return L_Out.True;
  } catch {
    return L_Report.L_ReportErr(env, proveIfExec, proveNode);
  }
}
