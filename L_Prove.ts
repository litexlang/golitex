import { L_Out } from "./L_Structs";
import { L_Env } from "./L_Env";
import { nodeExec, noVarsOrOptDeclaredHere } from "./L_Executor";
import { L_Node, OptNode, PostfixProve } from "./L_Nodes";
import * as L_Checker from "./L_Checker";
import * as L_Memory from "./L_Memory";
import { reportExecL_Out, reportNewExist } from "./L_Messages";
// import { existBuiltinCheck } from "./L_Builtins";

export function proveOpt(env: L_Env, toProve: OptNode, block: L_Node[]): L_Out {
  try {
    const newEnv = new L_Env(env);

    for (const subNode of block) {
      const out = nodeExec(newEnv, subNode, false);
      env.newMessage(reportExecL_Out(out, toProve));
      if (out === L_Out.Error) {
        newEnv.getMessages().forEach((e) => env.newMessage(e));
        env.newMessage(`Errors: Failed to execute ${subNode}`);
        return L_Out.Error;
      }
    }

    const ok = noVarsOrOptDeclaredHere(env, newEnv, toProve);
    if (!ok) return L_Out.Error;

    const out = L_Checker.checkFact(newEnv, toProve);
    if (out !== L_Out.True) return out;

    L_Memory.newFact(env, toProve);

    newEnv.getMessages().forEach((e) => env.newMessage(`[prove] ${e}`));

    return L_Out.True;
  } catch {
    env.newMessage(`${toProve}`);
    return L_Out.Error;
  }
}

export function proveOptByContradict(
  env: L_Env,
  toProve: OptNode,
  block: L_Node[],
  contradict: OptNode
): L_Out {
  try {
    const newEnv = new L_Env(env);

    toProve.isT = !toProve.isT;
    let ok = L_Memory.newFact(newEnv, toProve);
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

    let out = L_Checker.checkFact(newEnv, contradict);
    if (out !== L_Out.True) {
      env.newMessage(`Errors: Failed to execute ${contradict}`);
      return L_Out.Error;
    }

    contradict.isT = !contradict.isT;
    out = L_Checker.checkFact(newEnv, contradict);
    if (out !== L_Out.True) {
      env.newMessage(`Errors: Failed to execute ${contradict}`);
      return L_Out.Error;
    }

    ok = noVarsOrOptDeclaredHere(env, newEnv, toProve);
    if (!ok) return L_Out.Error;

    toProve.isT = !toProve.isT;
    ok = L_Memory.newFact(env, toProve);
    if (!ok) {
      env.newMessage(`Failed to store ${toProve}`);
      return L_Out.Error;
    }

    newEnv
      .getMessages()
      .forEach((e) => env.newMessage(`[prove_by_contradict] ${e}`));

    return L_Out.True;
  } catch {
    env.newMessage(`${toProve}`);
    return L_Out.Error;
  }
}

export function postfixProveExec(
  env: L_Env,
  postfixProve: PostfixProve
): L_Out {
  try {
    const newEnv = new L_Env(env);
    for (const subNode of postfixProve.block) {
      const out = nodeExec(newEnv, subNode, false);
      if (out !== L_Out.True) {
        newEnv.getMessages().forEach((e) => env.newMessage(e));
        env.newMessage(`${postfixProve} failed.`);
        return out;
      }
    }

    for (const fact of postfixProve.facts) {
      const ok = noVarsOrOptDeclaredHere(env, newEnv, fact);
      if (!ok) return L_Out.Error;
    }

    for (const fact of postfixProve.facts) {
      const out = L_Checker.checkFact(newEnv, fact);
      if (out !== L_Out.True) {
        newEnv.getMessages().forEach((e) => env.newMessage(e));
        env.newMessage(`${postfixProve} failed.`);
        return out;
      }
    }

    for (const fact of postfixProve.facts) {
      const ok = L_Memory.newFact(env, fact);
      if (!ok) {
        env.newMessage(`Failed to store ${fact}`);
        return L_Out.Error;
      }
    }

    newEnv.getMessages().forEach((e) => env.newMessage(`[prove] ${e}`));

    // store named knowns
    for (const [i, key] of postfixProve.names.entries()) {
      const ok = env.newNamedKnownToCheck(key, postfixProve.facts[i]);
      if (!ok) throw Error();
    }

    return L_Out.True;
  } catch {
    env.newMessage("by error");
    return L_Out.Error;
  }
}

// export function proveExist(
//   env: L_Env,
//   toProve: OptNode,
//   block: L_Node[]
// ): L_Out {
//   try {
//     const newEnv = new L_Env(env);
//     for (const node of block) {
//       const out = nodeExec(newEnv, node, true);
//       if (out !== L_Out.True) return out;
//     }

//     const out = existBuiltinCheck(newEnv, toProve);
//     if (out !== L_Out.True) return out;

//     env.newExist(toProve.name, new KnownExist(toProve.isT));
//     return reportNewExist(env, toProve);
//   } catch {
//     return env.errMesReturnL_Out(toProve);
//   }
// }
