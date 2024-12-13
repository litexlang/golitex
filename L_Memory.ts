import {
  BuiltinCheckNode,
  DefNode,
  IfNode,
  IsPropertyNode,
  LogicNode,
  OptNode,
  ToCheckNode,
} from "./L_Nodes";
import { L_Env } from "./L_Env";
import { reportStoreErr } from "./L_Messages";

export function declNewFact(env: L_Env, node: DefNode): boolean {
  let ok = true;
  ok = env.newDef(node.opt.optSymbol.name, node);
  for (const onlyIf of node.onlyIfs) {
    const ok = newFact(env, onlyIf);
    if (!ok) return env.errMesReturnBoolean(`Failed to store ${onlyIf}`);
  }
  return ok;
}

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
    const roots: [OptNode, IfNode[]][] = fact.getRootNodes();
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
