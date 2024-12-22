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

export function compositeSatisfyItsReq(
  env: L_Env,
  composite: L_Composite
): boolean {
  try {
    const declaration = env.getCompositeVar(composite.name);

    if (declaration === undefined) {
      env.report(`[Error] ${composite.name} undeclared`);
      throw Error();
    }

    if (composite.values.length !== declaration.composite.values.length) {
      throw Error();
    }

    const freeFixPairs: [L_Symbol, L_Symbol][] = LogicNode.makeFreeFixPairs(
      env,
      composite.values,
      declaration.composite.values
    );

    const newFacts = declaration.facts.map((e) => e.fix(env, freeFixPairs));

    for (const fact of newFacts) {
      if (checkFact(env, fact) !== L_Out.True) {
        return false;
      }
    }

    return true;
  } catch {
    return L_ReportBoolErr(env, compositeSatisfyItsReq, ``);
  }
}
