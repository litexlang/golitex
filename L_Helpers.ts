import { L_Env } from "./L_Env";
import {
  FactsNode,
  IfNode,
  L_FactNode,
  LogicNode,
  OptFactNode,
} from "./L_Nodes";
import { L_Singleton, L_Symbol } from "./L_Symbols";

class FactVarsDeclaredChecker {
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
      try {
        v.tryVarsDeclared(env);
      } catch (error) {
        if (error instanceof Error)
          error.message += `variable ${v} in ${fact} not declared.\n`;
        throw error;
      }
    }

    if (fact.checkVars === undefined) return;

    for (const layer of fact.checkVars) {
      for (const v of layer) {
        try {
          v.tryVarsDeclared(env);
        } catch (error) {
          if (error instanceof Error)
            error.message += `variable ${v} in ${fact} not declared.\n`;
          throw error;
        }
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
      req.tryFactVarsDeclared(newEnv);
    }

    for (const onlyIf of fact.onlyIfs) {
      onlyIf.tryFactVarsDeclared(newEnv);
    }
  }

  private static checkFactsNode(env: L_Env, fact: FactsNode): void {
    for (const v of fact.varsPairs) {
      v.forEach((e) => e[1].tryVarsDeclared(env));
    }

    for (const f of fact.facts) {
      f.tryFactVarsDeclared(env);
    }
  }
}

class SymbolDeclaredChecker {
  static check(env: L_Env, symbol: L_Symbol): boolean {
    if (symbol instanceof L_Singleton) {
      return this.checkSingleton(env, symbol);
    }

    throw Error();
  }

  private static messageVarNotDeclared(varNotDeclared: string): string {
    return `Not Declared: ${varNotDeclared}`;
  }

  private static checkSingleton(env: L_Env, symbol: L_Singleton): boolean {
    if (env.isSingletonDeclared(symbol.value)) return true;
    else throw Error(this.messageVarNotDeclared(symbol.value));
  }
}
