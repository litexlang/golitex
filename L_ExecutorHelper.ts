import { checkFact } from "./L_Checker";
import { L_Env } from "./L_Env";
import { LogicNode, ToCheckNode } from "./L_Nodes";
import { L_ReportBoolErr } from "./L_Report";
import { L_Composite, L_Out, L_Symbol } from "./L_Structs";

export function optsVarsDeclaredInFacts(
  env: L_Env,
  facts: ToCheckNode[]
): boolean {
  for (const f of facts) {
    const ok = env.subFactsDeclaredOrBuiltin(f);
    if (!ok) {
      //TODO I SHOULD IMPLEMENT check whether something is declared when checking
    }
  }

  for (const f of facts) {
    if (!f.varsDeclared(env)) {
      env.report(`[Error] Not all of related variables are declared.`);
      return false;
    }
  }

  return true;
}
