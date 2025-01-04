import { L_Env } from "./L_Env";
import {
  FactsNode,
  IfNode,
  L_FactNode,
  LogicNode,
  OptFactNode,
} from "./L_Facts";
import { SymbolDeclaredChecker } from "./L_SymbolsHelper";

export class FactVarsDeclaredChecker {
  static check(env: L_Env, fact: L_FactNode): void {
    if (fact instanceof OptFactNode) {
      return this.checkOpt(env, fact);
    } else if (fact instanceof IfNode) {
      return this.checkLogicNode(env, fact);
    } else if (fact instanceof FactsNode) {
      return this.checkFactsNode(env, fact);
    }

    throw Error();
  }

  private static checkOpt(env: L_Env, fact: OptFactNode): void {
    for (const v of fact.vars) {
      // v.tryVarsDeclared(env);
      SymbolDeclaredChecker.check(env, v);
    }

    if (fact.checkVars === undefined) return;

    for (const layer of fact.checkVars) {
      for (const v of layer) {
        // v.tryVarsDeclared(env);
        SymbolDeclaredChecker.check(env, v);
      }
    }

    return;
  }

  private static checkLogicNode(env: L_Env, fact: LogicNode): void {
    const newEnv = new L_Env(env);
    for (const v of fact.vars) {
      newEnv.tryNewPureSingleton(v.value);
    }

    for (const formReq of fact.varsFormReq) {
      formReq.freeVars.forEach((e) => newEnv.tryNewPureSingleton(e.value));
    }

    for (const req of fact.req) {
      // req.tryFactVarsDeclared(newEnv);
      this.check(newEnv, req);
    }

    for (const onlyIf of fact.onlyIfs) {
      // onlyIf.tryFactVarsDeclared(newEnv);
      this.check(newEnv, onlyIf);
    }
  }

  private static checkFactsNode(env: L_Env, fact: FactsNode): void {
    for (const v of fact.varsPairs) {
      // v.forEach((e) => e[1].tryVarsDeclared(env));
      // v.forEach((e) => this.check(env, e[1]));
      v.forEach((e) => SymbolDeclaredChecker.check(env, e[1]));
    }

    for (const f of fact.facts) {
      // f.tryFactVarsDeclared(env);
      this.check(env, f);
    }
  }
}
