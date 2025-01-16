import { L_Out } from "./L_Structs";
import { L_Env } from "./L_Env";
import { L_Exec } from "./L_Executor";
import { OptFactNode } from "./L_Facts";
import { L_Node } from "./L_Nodes";
import * as L_Checker from "./L_Checker";
import * as L_Memory from "./L_Memory";
import * as L_Report from "./L_Report";

export function proveOpt(
  env: L_Env,
  toProve: OptFactNode,
  block: L_Node[]
): L_Out {
  try {
    const newEnv = new L_Env(env);

    for (const subNode of block) {
      const out = L_Exec(newEnv, subNode);
      if (out === L_Out.Error) {
        newEnv.getMessages().forEach((e) => env.report(e));
        env.report(`Errors: Failed to execute ${subNode}`);
        return L_Out.Error;
      }
      return L_Report.reportL_Out(env, out, toProve);
    }

    // const ok = toProve.varsDeclared(env);
    // if (!ok) {
    //   return L_Report.L_ReportErr(
    //     env,
    //     proveOptByContradict,
    //     `[Error] parameters in ${toProve} must be declared outside`
    //   );
    // }

    const out = L_Checker.checkFact(newEnv, toProve);
    if (out !== L_Out.True) return out;

    L_Memory.tryNewFact(env, toProve);

    newEnv.getMessages().forEach((e) => env.report(`[prove] ${e}`));

    return L_Out.True;
  } catch {
    env.report(`${toProve}`);
    return L_Out.Error;
  }
}

export function proveOptByContradict(
  env: L_Env,
  toProve: OptFactNode,
  block: L_Node[],
  contradict: OptFactNode
): L_Out {
  try {
    const newEnv = new L_Env(env);

    toProve.isT = !toProve.isT;
    L_Memory.tryNewFact(newEnv, toProve);
    // ok = toProve.varsDeclared(env);
    // if (!ok) {
    //   return L_Report.L_ReportErr(
    //     env,
    //     proveOptByContradict,
    //     `[Error] parameters in ${toProve} must be declared outside`
    //   );
    // }

    for (const subNode of block) {
      const out = L_Exec(newEnv, subNode);
      if (out === L_Out.Error) {
        newEnv.getMessages().forEach((e) => env.report(e));
        env.report(`Errors: Failed to execute ${subNode}`);
        return L_Out.Error;
      }
    }

    let out = L_Checker.checkFact(newEnv, contradict);
    if (out !== L_Out.True) {
      env.report(`Errors: Failed to execute ${contradict}`);
      return L_Out.Error;
    }

    contradict.isT = !contradict.isT;
    out = L_Checker.checkFact(newEnv, contradict);
    if (out !== L_Out.True) {
      env.report(`Errors: Failed to execute ${contradict}`);
      return L_Out.Error;
    }

    toProve.isT = !toProve.isT;
    L_Memory.tryNewFact(env, toProve);
    // if (!ok) {
    //   env.report(`Failed to store ${toProve}`);
    //   return L_Out.Error;
    // }

    newEnv
      .getMessages()
      .forEach((e) => env.report(`[prove_by_contradict] ${e}`));

    return L_Out.True;
  } catch {
    env.report(`${toProve}`);
    return L_Out.Error;
  }
}
