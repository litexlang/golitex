import {
  FormulaFactNode,
  BuiltinCheckNode,
  IfNode,
  IsConceptNode,
  OptFactNode,
  L_FactNode,
  FactsNode,
} from "./L_Facts";
import { L_Env } from "./L_Env";
import { reportStoreErr } from "./L_Report";
import {
  FormulaKnownFactReq,
  IfKnownFactReq,
  OptKnownFactReq,
  OptSymbol,
} from "./L_Structs";

export function tryNewFact(env: L_Env, fact: L_FactNode): void {
  try {
    if (fact instanceof BuiltinCheckNode) {
      newBuiltinFact(env, fact);
    } else if (fact instanceof IfNode) {
      tryNewIfThenFact(env, fact);
    } else if (fact instanceof OptFactNode) {
      newOptFact(env, fact);
    } else if (fact instanceof FormulaFactNode) {
      tryNewFormulaFact(env, fact);
    } else if (fact instanceof FactsNode) {
      tryNewFactsNode(env, fact);
    } else {
      throw Error();
    }

    env.report(`[fact] ${fact}`);
  } catch (error) {
    env.report(`failed to store ${fact}`);
    reportStoreErr(env, tryNewFact.name, fact);
    throw error;
  }
}

function tryNewFactsNode(env: L_Env, fact: FactsNode): void {
  try {
    const freeFixPairs = fact.varsPairs.flat();
    const newFacts = fact.facts.map((e) => e.fixByIfVars(env, freeFixPairs));
    newFacts.forEach((fact) => tryNewFact(env, fact));
  } catch (error) {
    reportStoreErr(env, tryNewFactsNode.name, fact);
    throw error;
  }
}

function tryNewIfThenFact(env: L_Env, fact: IfNode): void {
  try {
    const roots = fact.getRootOptNodes();
    roots.forEach((root) =>
      env.tryNewFact(
        root[0].optSymbol.name,
        new IfKnownFactReq([...root[1], root[0]])
      )
    );
  } catch (error) {
    reportStoreErr(env, tryNewIfThenFact.name, fact);
    throw error;
  }
}

function newOptFact(env: L_Env, fact: OptFactNode): void {
  try {
    env.tryNewFact(fact.optSymbol.name, new OptKnownFactReq(fact));
  } catch (error) {
    reportStoreErr(env, newOptFact.name, fact);
    throw error;
  }
}

function tryNewFormulaFact(env: L_Env, fact: FormulaFactNode): void {
  try {
    const roots = fact.getRootOptNodes();
    roots.forEach((root) =>
      env.tryNewFact(
        root[0].optSymbol.name,
        new FormulaKnownFactReq([...root[1], root[0]])
      )
    );
  } catch (error) {
    reportStoreErr(env, tryNewFormulaFact.name, fact);
    throw error;
  }
}

function newBuiltinFact(env: L_Env, fact: L_FactNode): void {
  try {
    if (fact instanceof IsConceptNode) {
      return;
    } else if (fact instanceof BuiltinCheckNode) {
      return;
    }

    return;
  } catch (error) {
    reportStoreErr(env, newBuiltinFact.name, fact);
    throw error;
  }
}
