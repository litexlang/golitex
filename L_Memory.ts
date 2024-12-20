import {
  ToCheckFormulaNode,
  BuiltinCheckNode,
  DefNode,
  IfNode,
  IsPropertyNode,
  LogicNode,
  OptNode,
  ToCheckNode,
  AndToCheckNode,
  OrToCheckNode,
} from "./L_Nodes";
import { L_Env } from "./L_Env";
import { reportStoreErr } from "./L_Report";

export function newFact(env: L_Env, fact: ToCheckNode): boolean {
  if (fact instanceof BuiltinCheckNode) {
    const ok = newBuiltinFact(env, fact);
    return ok;
  }

  try {
    if (fact instanceof IfNode) {
      const ok = newIfThenFact(env, fact as IfNode);
      if (!ok) return false;
    } else if (fact instanceof OptNode) {
      const ok = newOptFact(env, fact);
      if (!ok) return false;
    } else if (fact instanceof ToCheckFormulaNode) {
      const ok = newFormulaFact(env, fact);
      if (!ok) return false;
    } else {
      throw Error();
    }

    return env.OKMesReturnBoolean(`[new fact] ${fact}`);
  } catch {
    return reportStoreErr(env, newFact.name, fact);
  }
}

function newIfThenFact(env: L_Env, fact: IfNode): boolean {
  try {
    const roots = fact.getRootOptNodes();
    roots.forEach((root) => env.newFact(root[0].optSymbol.name, fact));
    return true;
  } catch {
    return reportStoreErr(env, newIfThenFact.name, fact);
  }
}

function newOptFact(env: L_Env, fact: OptNode): boolean {
  try {
    return env.newFact(fact.optSymbol.name, fact);
  } catch {
    return reportStoreErr(env, newOptFact.name, fact);
  }
}

function newFormulaFact(env: L_Env, fact: ToCheckFormulaNode): boolean {
  try {
    const roots: OptNode[] = fact.getRootOptNodes().map((e) => e[0]);
    roots.forEach((root) => env.newFact(root.optSymbol.name, fact));
    if (fact instanceof AndToCheckNode) {
      newFact(env, fact.left);
      newFact(env, fact.right);
    } else if (fact instanceof OrToCheckNode) {
      //! to make "if x : (p(x) or t(x)) {(p(x) or t(x))}" work, I must make or into if-then
      const equivalentIfs = fact.getEquivalentIfs();
      if (equivalentIfs !== null) {
        equivalentIfs.forEach((ifFact) => newFact(env, ifFact));
      }
    }
    return true;
  } catch {
    return reportStoreErr(env, newFormulaFact.name, fact);
  }
}

function newBuiltinFact(env: L_Env, fact: ToCheckNode): boolean {
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
