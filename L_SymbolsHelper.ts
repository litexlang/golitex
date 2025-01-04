import { L_Env } from "./L_Env";
import { IndexedSymbol, L_Composite, L_Singleton, L_Symbol } from "./L_Symbols";

export class SymbolDeclaredChecker {
  static check(env: L_Env, symbol: L_Symbol): void {
    if (symbol instanceof L_Singleton) {
      return this.checkSingleton(env, symbol);
    } else if (symbol instanceof L_Composite) {
      return this.checkComposite(env, symbol);
    } else if (symbol instanceof IndexedSymbol) {
      return this.checkIndexedSymbol(env, symbol);
    }

    throw Error();
  }

  private static errMessage(varNotDeclared: string): string {
    return `Not Declared: ${varNotDeclared}`;
  }

  private static checkSingleton(env: L_Env, symbol: L_Singleton): void {
    if (env.isSingletonDeclared(symbol.value)) return;
    else throw Error(this.errMessage(symbol.value));
  }

  private static checkComposite(env: L_Env, symbol: L_Composite): void {
    if (env.getCompositeVar(symbol.name) === undefined) return;

    for (const value of symbol.values) {
      // value.tryVarsDeclared(env);
      this.check(env, value);
    }
  }

  private static checkIndexedSymbol(env: L_Env, symbol: IndexedSymbol): void {
    // symbol.given.tryVarsDeclared(env);
    this.check(env, symbol.given);
  }
}
