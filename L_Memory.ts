import {
  FormulaFactNode,
  BuiltinCheckNode,
  DefConceptNode,
  IfNode,
  IsPropertyNode,
  LogicNode,
  OptFactNode,
  L_FactNode,
  AndToCheckNode,
  OrToCheckNode,
} from "./L_Nodes";
import { L_Env } from "./L_Env";
import { reportStoreErr } from "./L_Report";
import {
  FormulaKnownFactReq,
  IfKnownFactReq,
  L_KnownFactReq,
  OptKnownFactReq,
} from "./L_Structs";

export function newFact(env: L_Env, fact: L_FactNode): boolean {
  if (fact instanceof BuiltinCheckNode) {
    const ok = newBuiltinFact(env, fact);
    return ok;
  }

  try {
    if (fact instanceof IfNode) {
      const ok = newIfThenFact(env, fact as IfNode);
      if (!ok) return false;
    } else if (fact instanceof OptFactNode) {
      const ok = newOptFact(env, fact);
      if (!ok) return false;
    } else if (fact instanceof FormulaFactNode) {
      const ok = newFormulaFact(env, fact);
      if (!ok) return false;
    } else {
      throw Error();
    }

    return env.OKMesReturnBoolean(`[fact] ${fact}`);
  } catch {
    return reportStoreErr(env, newFact.name, fact);
  }
}

function newIfThenFact(env: L_Env, fact: IfNode): boolean {
  try {
    const roots = fact.getRootOptNodes();
    roots.forEach((root) =>
      env.newFact(
        root[0].optSymbol.name,
        new IfKnownFactReq([...root[1], root[0]])
      )
    );
    return true;
  } catch {
    return reportStoreErr(env, newIfThenFact.name, fact);
  }
}

function newOptFact(env: L_Env, fact: OptFactNode): boolean {
  try {
    return env.newFact(fact.optSymbol.name, new OptKnownFactReq(fact));
  } catch {
    return reportStoreErr(env, newOptFact.name, fact);
  }
}

function newFormulaFact(env: L_Env, fact: FormulaFactNode): boolean {
  try {
    const roots = fact.getRootOptNodes();
    roots.forEach((root) =>
      env.newFact(
        root[0].optSymbol.name,
        new FormulaKnownFactReq([...root[1], root[0]])
      )
    );

    return true;
  } catch {
    return reportStoreErr(env, newFormulaFact.name, fact);
  }
}

function newBuiltinFact(env: L_Env, fact: L_FactNode): boolean {
  try {
    if (fact instanceof IsPropertyNode) {
      return true;
    } else if (fact instanceof BuiltinCheckNode) {
      return true;
    }

    return false;
  } catch {
    return reportStoreErr(env, newBuiltinFact.name, fact);
  }
}
