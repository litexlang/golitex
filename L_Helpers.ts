import { L_Env } from "./L_Env";
import { L_FactNode, OptFactNode } from "./L_Nodes";
import { L_Singleton, L_Symbol } from "./L_Symbols";

class FactVarsDeclaredChecker {
  static check(env: L_Env, fact: L_FactNode): boolean {
    if (fact instanceof OptFactNode) {
    }

    throw Error();
  }

  private static checkOpt(env: L_Env, fact: OptFactNode): boolean {
    for (const v of fact.vars) {
    }

    throw Error();
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
