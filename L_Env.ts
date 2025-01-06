import * as L_Nodes from "./L_Nodes";
import * as L_Structs from "./L_Structs";
import { L_KW } from "./L_Keywords";
import { L_Singleton, L_Symbol } from "./L_Symbols";
import { EqualSymbol, EqualOptSymbol } from "./L_OptSymbol";
import * as L_Facts from "./L_Facts";

export class L_Env {
  private parent: L_Env | undefined = undefined;
  private messages: string[] = [];
  private singletonVars = new Set<string>();
  private concepts = new Map<string, L_Nodes.DefConceptNode>();
  private facts = new Map<string, L_Structs.L_KnownFactReq[]>();
  private operators = new Map<string, L_Nodes.DefOperatorNode>();
  private regexSingletons = new Map<string, L_Nodes.LetsNode>();
  private includes: string[] = [];
  private literalOperators = new Map<string, L_Nodes.DefLiteralOptNode>();
  private symbolAliases = new Map<string, L_Symbol[]>();
  private formalSymbols = new Set<string>();
  private conceptAliasMap = new Map<string, Set<string>>();

  constructor(parent: L_Env | undefined = undefined) {
    this.parent = parent;
  }

  static constructWithInitialization(): L_Env {
    const env = new L_Env();

    // Initialize equal
    const opt = new L_Facts.OptFactNode(
      EqualSymbol,
      [new L_Singleton("x"), new L_Singleton("y")],
      true,
      undefined
    );
    const equalOpt = new L_Facts.EqualFact(opt);
    env.tryNewDef(L_KW.Equal, new L_Nodes.DefConceptNode(opt, [], [], true));

    return env;
  }

  tryNewConceptAlias(node: L_Nodes.ConceptAliasNode): void {
    if (this.getDefOperator(node.name) !== undefined) {
      throw Error(`The concept alias ${node.name} is already declared.`);
    } else {
      const relatedMap = this.getConceptAlias(node.toBeAliased);

      let originalDef = this.getConcept(node.toBeAliased);
      if (originalDef === undefined) {
        throw Error(`${node.toBeAliased} is not declared.`);
      } else {
        // TODO
        this.tryNewDef(node.name, originalDef);
      }

      if (relatedMap === undefined) {
        const newMap = new Set<string>();
        newMap.add(node.toBeAliased);
        this.conceptAliasMap.set(node.toBeAliased, newMap);
        newMap.add(node.name);
        this.conceptAliasMap.set(node.name, newMap);
      } else {
        relatedMap.add(node.name);
        this.conceptAliasMap.set(node.name, relatedMap);
      }
    }
  }

  getConceptAlias(key: string): undefined | Set<string> {
    const out = this.conceptAliasMap.get(key);
    if (out !== undefined) {
      return out;
    } else {
      if (this.parent !== undefined) {
        return this.parent.getConceptAlias(key);
      } else {
        return undefined;
      }
    }
  }

  tryNewLiteralOpt(node: L_Nodes.DefLiteralOptNode): void {
    if (this.getLiteralOpt(node.name)) {
      throw Error(`The literal operator ${node.name} is already declared.`);
    } else {
      this.literalOperators.set(node.name, node);
    }
  }

  getLiteralOpt(key: string): undefined | L_Nodes.DefLiteralOptNode {
    const out = this.literalOperators.get(key);
    if (out !== undefined) {
      return out;
    } else {
      if (this.parent !== undefined) {
        return this.parent.getLiteralOpt(key);
      } else {
        return undefined;
      }
    }
  }

  tryNewComposite(key: string, fact: L_Nodes.DefOperatorNode): void {
    if (this.getDefOperator(key)) {
      throw Error(
        `The variable "${key}" is already declared in this environment or its parent environments. Please use a different name.`
      );
      // return L_ReportBoolErr(this, this.tryNewComposite);
    } else {
      this.operators.set(key, fact);
      // return true;
    }
  }

  // newFunctionalSymbol(
  //   key: string,
  //   fact: L_Nodes.DefFunctionalSymbolNode
  // ): boolean {
  //   if (this.getFunctionalSymbol(key)) {
  //     return L_ReportBoolErr(
  //       this,
  //       this.newFunctionalSymbol,
  //       `The variable "${key}" is already declared in this environment or its parent environments. Please use a different name.`
  //     );
  //   } else {
  //     this.functionalSymbols.set(key, fact);
  //     return true;
  //   }
  // }

  // getFunctionalSymbol(
  //   key: string
  // ): undefined | L_Nodes.DefFunctionalSymbolNode {
  //   const out = this.functionalSymbols.get(key);
  //   if (out !== undefined) {
  //     return out;
  //   } else {
  //     if (this.parent !== undefined) {
  //       return this.parent.getFunctionalSymbol(key);
  //     } else {
  //       return undefined;
  //     }
  //   }
  // }

  getDefOperator(key: string): undefined | L_Nodes.DefOperatorNode {
    const out = this.operators.get(key);
    if (out !== undefined) {
      return out;
    } else {
      if (this.parent !== undefined) {
        return this.parent.getDefOperator(key);
      } else {
        return undefined;
      }
    }
  }

  tryNewFact(key: string, fact: L_Structs.L_KnownFactReq): void {
    if (this.facts.get(key) === undefined) {
      this.facts.set(key, [fact]);
    } else {
      this.facts.get(key)?.push(fact);
    }
  }

  getFacts(key: string): undefined | L_Structs.L_KnownFactReq[] {
    let currentFacts = this.facts.get(key);
    const aliases = this.getConceptAlias(key);
    aliases?.forEach((alias) => {
      if (currentFacts === undefined) {
        currentFacts = this.facts.get(alias);
      } else {
        const aliasFacts = this.facts.get(alias);
        if (aliasFacts !== undefined)
          currentFacts = [...currentFacts, ...aliasFacts];
      }
    });

    if (currentFacts === undefined) {
      if (this.parent !== undefined) {
        return this.parent.getFacts(key);
      } else {
        return undefined;
      }
    } else {
      const fromParent = this.parent?.getFacts(key);
      if (fromParent === undefined) {
        return currentFacts;
      } else {
        return [...currentFacts, ...fromParent];
      }
    }
  }

  clear() {
    this.parent = undefined;
    this.messages = [];
    this.singletonVars = new Set<string>();
    this.regexSingletons = new Map<string, L_Nodes.LetsNode>();
    this.concepts = new Map<string, L_Nodes.DefConceptNode>();
  }

  // used by checker and executor
  tryFactDeclaredOrBuiltin(node: L_Facts.L_FactNode): void {
    if (node instanceof L_Facts.BuiltinCheckNode) {
      return;
    } else if (node instanceof L_Facts.OptFactNode) {
      if (this.getConcept(node.optSymbol.name) !== undefined) return;
      else throw Error(`operator ${node.optSymbol.name} is not declared`);
    } else if (node instanceof L_Facts.LogicNode) {
      node.req.forEach((e) => this.tryFactDeclaredOrBuiltin(e));
      node.onlyIfs.forEach((e) => this.tryFactDeclaredOrBuiltin(e));
    } else if (node instanceof L_Facts.FormulaFactNode) {
      this.tryFactDeclaredOrBuiltin(node.left);
      this.tryFactDeclaredOrBuiltin(node.right);
    }
  }

  getConcept(s: string): L_Nodes.DefConceptNode | undefined {
    if (this.concepts.has(s)) {
      return this.concepts.get(s);
    } else if (this.parent) {
      return this.parent.getConcept(s);
    } else {
      return undefined;
    }
  }

  tryNewDef(s: string, defNode: L_Nodes.DefConceptNode): void {
    // REMARK: YOU ARE NOT ALLOWED TO DECLARE A FACT TWICE AT THE SAME ENV.
    if (this.getConcept(s) !== undefined) {
      throw Error(
        `The operator "${s}" is already declared in this environment or its parent environments. Please use a different name.`
      );
    }

    this.concepts.set(s, defNode);
    this.report(`[${L_KW.DefConcept}] ${defNode}`);
  }

  tryNewLetsSymbol(letsNode: L_Nodes.LetsNode) {
    if (this.isSingletonDeclared(letsNode.name)) {
      throw Error(`letsVar ${letsNode.name} already declared`);
    }
    this.regexSingletons.set(letsNode.name, letsNode);
  }

  tryNewSingleton(fix: string): void {
    // TO MAKE MY LIFE EASIER SO THAT I DO NOT NEED TO BIND ENV TO VARIABLE, I forbid redefining a variable with the same name with any visible variable.
    if (this.isSingletonDeclared(fix)) {
      throw Error(
        `The variable "${fix}" is already declared in this environment or its parent environments. Please use a different name.`
      );
    }
    this.singletonVars.add(fix);
  }

  tryNewFormalSymbol(fix: string): void {
    // TO MAKE MY LIFE EASIER SO THAT I DO NOT NEED TO BIND ENV TO VARIABLE, I forbid redefining a variable with the same name with any visible variable.
    if (this.isSingletonDeclared(fix)) {
      throw Error(
        `The variable "${fix}" is already declared in this environment or its parent environments. Please use a different name.`
      );
    }
    this.formalSymbols.add(fix);
  }

  tryNewAlias(name: L_Singleton, toBeAliased: L_Symbol[]): void {
    if (this.isSingletonDeclared(name.value)) {
      throw Error(
        `The variable "${name.value}" is already declared in this environment or its parent environments. Please use a different name.`
      );
    }

    this.symbolAliases.set(name.value, toBeAliased);
  }

  getAlias(name: string): L_Symbol[] | undefined {
    const out = this.symbolAliases.get(name);
    if (out === undefined) {
      if (this.parent !== undefined) {
        return this.parent.getAlias(name);
      } else {
        return undefined;
      }
    } else {
      return out;
    }
  }

  //* A VERY IMPORTANT FUNCTION. IT GUARANTEES SAFETY.
  isSingletonDeclared(fix: string): boolean {
    return (
      this.isKeywordSingleton(fix) ||
      this.isPureSingletonDeclared(fix) ||
      this.isRegexSingleton(fix) ||
      this.isFormalSymbolDeclared(fix) ||
      this.isAlias(fix)
    );
  }

  isKeywordSingleton(fix: string): boolean {
    return fix === L_KW.AnySymbol || fix === L_KW.ExistSymbol;
  }

  isAlias(name: string): boolean {
    if (this.getAlias(name) !== undefined) {
      return true;
    } else {
      if (!this.parent) return false;
      else return this.parent.isAlias(name);
    }
  }

  // two ways of checking : 1. it's letsVar name 2. it satisfies regex of a var
  isRegexSingleton(varStr: string): boolean {
    if (this.regexSingletons.has(varStr)) {
      return true;
    }

    for (const knownLet of this.regexSingletons.values()) {
      if (knownLet.regex.test(varStr)) return true;
    }

    if (this.parent !== undefined) {
      return this.parent.isRegexSingleton(varStr);
    } else return false;
  }

  isFormalSymbolDeclared(key: string): boolean {
    if (this.formalSymbols.has(key)) {
      return true;
    } else {
      if (!this.parent) return false;
      else return this.parent.isFormalSymbolDeclared(key);
    }
  }

  isPureSingletonDeclared(key: string): boolean {
    if (this.singletonVars.has(key)) {
      return true;
    } else {
      if (!this.parent) return false;
      else return this.parent.isPureSingletonDeclared(key);
    }
  }

  optDeclared(key: string): boolean {
    if (this.concepts.get(key)) {
      return true;
    } else {
      if (!this.parent) return false;
      else return this.parent.optDeclared(key);
    }
  }

  getMessages() {
    return this.messages;
  }

  report(s: string): L_Structs.L_Out {
    this.messages.push(s);
    return L_Structs.L_Out.True;
  }

  printClearMessage() {
    this.messages.forEach((m) => console.log(m));
    this.messages = [];
  }

  clearMessages() {
    this.messages = [];
  }

  // OKMesReturnL_Out(message: L_Nodes.L_Node | string): L_Structs.L_Out {
  //   if (message instanceof L_Nodes.L_Node) this.report(`OK! ${message}`);
  //   else this.report(message);
  //   return L_Structs.L_Out.True;
  // }

  // OKMesReturnBoolean(message: L_Nodes.L_Node | string): boolean {
  //   if (message instanceof L_Nodes.L_Node) this.report(`OK! ${message}`);
  //   else this.report(message);
  //   return true;
  // }

  // errMesReturnL_Out(s: L_Nodes.L_Node | string): void {
  //   this.report(`Error: ${s}`);
  //   // return L_Structs.L_Out.Error;
  // }

  // errMesReturnBoolean(s: L_Nodes.L_Node | string): boolean {
  //   this.report(`Error: ${s}`);
  //   return false;
  // }

  // printDeclFacts() {
  //   console.log("\n--Declared Facts--\n");

  //   for (const [name, declFact] of this.defs) {
  //     console.log(name);
  //     console.log(declFact);
  //   }
  // }

  toJSON() {
    return {
      vars: Array.from(this.singletonVars),
      defs: Object.fromEntries(this.concepts),
      facts: Object.fromEntries(this.facts),
    };
  }

  getLetsVar(varStr: string): L_Nodes.LetsNode | undefined {
    if (this.isRegexSingleton(varStr)) {
      const out = this.regexSingletons.get(varStr);
      if (out !== undefined) {
        return out;
      } else {
        for (const knownLet of this.regexSingletons.values()) {
          if (knownLet.regex.test(varStr)) return knownLet;
        }

        if (this.parent !== undefined) {
          return this.parent.getLetsVar(varStr);
        } else return undefined;
      }
    }

    return undefined;
  }

  // newMacro(macro: L_Nodes.MacroNode): boolean {
  //   if (this.getMacro(macro.name) !== undefined) {
  //     return L_ReportBoolErr(
  //       this,
  //       this.newMacro,
  //       `macro ${macro.name} is already declared.`
  //     );
  //   }
  //   this.macros.set(macro.name, macro);
  //   return true;
  // }

  // getMacro(name: string): L_Nodes.MacroNode | undefined {
  //   if (this.macros.has(name)) {
  //     return this.macros.get(name);
  //   }

  //   if (this.parent !== undefined) {
  //     return this.parent.getMacro(name);
  //   } else return undefined;
  // }

  tryNewInclude(path: string): void {
    if (!this.isLibPathIncluded(path)) {
      this.includes.push(path);
    } else {
      throw Error(`${path} is already included`);
    }
  }

  getIncludes(): string[] {
    if (this.parent === undefined) {
      return this.includes;
    } else {
      return [...this.parent.getIncludes(), ...this.includes];
    }
  }

  isLibPathIncluded(path: string): boolean {
    if (this.getIncludes().some((e) => e === path)) return true;
    else return false;
  }

  pushMessagesFromEnvReturnFalse(env: L_Env): boolean {
    this.messages.push(...env.getMessages());
    return false;
  }
}
