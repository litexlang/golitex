import {
  DefNode,
  L_Node,
  LetCompositeNode,
  LogicNode,
  MacroNode,
  OptNode,
  ToCheckNode,
} from "./L_Nodes";
import { examineStoredFact } from "./L_Memory";
import { L_KnownFact, L_OptSymbol, L_Out } from "./L_Structs";
import { isToCheckBuiltin } from "./L_Builtins";
import { KnownFact, StoredFact } from "./L_Structs";

export class L_Env {
  private parent: L_Env | undefined = undefined;
  private messages: string[] = [];
  private declaredVars = new Set<string>();
  private declaredHashVars = new Map<string, ToCheckNode[]>();
  private macros: MacroNode[] = [];
  private defs = new Map<string, DefNode>();
  private knownFacts = new Map<string, KnownFact>(); // key: operator name; value: stored layers of if-then that can be used to check operator.
  private namedKnownToChecks = new Map<string, ToCheckNode>();
  // private exists = new Map<string, KnownFact>();

  private facts = new Map<string, L_KnownFact[]>();
  private declaredComposites = new Map<string, LetCompositeNode>();

  constructor(parent: L_Env | undefined = undefined) {
    this.parent = parent;
  }

  newCompositeVar(key: string, fact: LetCompositeNode): boolean {
    if (this.declaredComposites.get(key)) {
      this.newMessage(`Failed: ${key} already declared.`);
      return false;
    } else {
      this.declaredComposites.set(key, fact);
      return true;
    }
  }

  getCompositeVar(key: string): undefined | LetCompositeNode {
    const out = this.declaredComposites.get(key);
    if (out !== undefined) {
      return out;
    } else {
      if (this.parent !== undefined) {
        return this.parent.getCompositeVar(key);
      } else {
        return undefined;
      }
    }
  }

  newFact(key: string, fact: L_KnownFact): boolean {
    if (this.facts.get(key) === undefined) {
      this.facts.set(key, [fact]);
    } else {
      this.facts.get(key)?.push(fact);
    }
    return true;
  }

  getFacts(key: string): undefined | L_KnownFact[] {
    const out = this.facts.get(key);
    if (out !== undefined) {
      return out;
    } else {
      if (this.parent !== undefined) {
        return this.parent.getFacts(key);
      } else {
        return undefined;
      }
    }
  }

  clear() {
    this.parent = undefined;
    this.messages = [];
    this.declaredVars = new Set<string>();
    this.macros = [];
    this.defs = new Map<string, DefNode>();
    this.knownFacts = new Map<string, KnownFact>();
    this.namedKnownToChecks = new Map<string, ToCheckNode>();
    // this.exists = new Map<string, KnownFact>();
  }

  // newExist(optName: string, exist: KnownFact): boolean {
  //   this.exists.set(optName, exist);
  //   return true;
  // }

  // isExisted(optName: string): boolean {
  //   if (this.exists.get(optName)?.isT === true) {
  //     return true;
  //   } else if (this.parent !== undefined) {
  //     return this.parent.isExisted(optName);
  //   } else {
  //     return false;
  //   }
  // }

  newHashVar(fix: string, facts: ToCheckNode[]): boolean {
    // TO MAKE MY LIFE EASIER SO THAT I DO NOT NEED TO BIND ENV TO VARIABLE, I forbid redefining a variable with the same name with any visible variable.
    if (this.hashVarDeclared(fix)) {
      this.newMessage(`${fix} already declared.`);
      return false;
    }
    this.declaredHashVars.set(fix, facts);
    return true;
  }

  hashVarDeclared(key: string): boolean {
    if (this.declaredHashVars.has(key)) {
      return true;
    } else {
      if (!this.parent) return false;
      else return this.parent.hashVarDeclared(key);
    }
  }

  getHashVarFacts(key: string): ToCheckNode[] | undefined {
    const toChecks = this.declaredHashVars.get(key);
    if (toChecks !== undefined) return toChecks;
    else if (this.parent !== undefined) {
      return this.parent.getHashVarFacts(key);
    } else return undefined;
  }

  newNamedKnownToCheck(name: string, toCheck: ToCheckNode): boolean {
    const out = this.getNamedKnownToCheck(name);
    if (out === undefined) {
      this.namedKnownToChecks.set(name, toCheck);
      return true;
    } else {
      return this.errMesReturnBoolean(
        `${name} is already a known fact. You can not double declare it.`
      );
    }
  }

  getNamedKnownToCheck(name: string): ToCheckNode | undefined {
    const known = this.namedKnownToChecks.get(name);
    if (known !== undefined) return known;
    else if (this.parent !== undefined) {
      return this.parent.getNamedKnownToCheck(name);
    } else return undefined;
  }

  getKnownFactsFromCurEnv(
    opt: OptNode,
    onlyRoot: boolean = false
  ): undefined | StoredFact[] {
    //*
    // const knownNodeRoot: KnownFact | undefined = this.knownFacts.get(
    //   opt.optSymbol
    // );
    // if (onlyRoot) {
    //   return knownNodeRoot?.getFactsToCheck([]);
    // }
    // if (knownNodeRoot !== undefined) {
    //   if (opt.checkVars === undefined) return knownNodeRoot.getFactsToCheck([]);
    //   else {
    //     const varsToCheckNumbers = opt.checkVars?.map((e) => e.length);
    //     if (varsToCheckNumbers === undefined) return undefined;
    //     return knownNodeRoot.getFactsToCheck(varsToCheckNumbers);
    //   }
    // } else {
    //   return undefined;
    // }
    //*
    return undefined;
  }

  newKnownFact(
    optName: L_OptSymbol,
    checkVars: string[][],
    fact: StoredFact
  ): boolean {
    // const ok = examineStoredFact(this, new OptNode(optName, fact.vars), fact);
    // if (!ok) return false;

    //*
    // const checkVarsNumLst = checkVars.map((e) => e.length);
    // const knownFact = this.knownFacts.get(optName);
    // if (knownFact === undefined) {
    //   let newKnownFact: KnownFact;
    //   if (fact instanceof StoredExist) {
    //     newKnownFact = new KnownExist();
    //   } else {
    //     newKnownFact = new KnownFact();
    //   }
    //   this.knownFacts.set(optName, newKnownFact);

    //   return newKnownFact.addChild(checkVarsNumLst, fact);
    // } else {
    //   return knownFact.addChild(checkVarsNumLst, fact);
    // }
    //*

    return false;
  }

  getMacros(previous: MacroNode[]): MacroNode[] {
    previous = [...previous, ...this.macros];
    if (this.parent !== undefined) {
      return this.parent.getMacros(previous);
    } else {
      return previous;
    }
  }

  newMacro(macroNode: MacroNode) {
    this.macros.push(macroNode);
  }

  factsInToCheckAllDeclared(node: ToCheckNode): boolean {
    if (node instanceof OptNode) {
      return (
        this.getDef(node.optSymbol.name) !== undefined || isToCheckBuiltin(node)
      );
    } else if (node instanceof LogicNode) {
      return (
        node.req.every((e) => this.factsInToCheckAllDeclared(e)) &&
        node.onlyIfs.every((e) => this.factsInToCheckAllDeclared(e))
      );
    }

    return false;
  }

  getDef(s: string): DefNode | undefined {
    if (this.defs.has(s)) {
      return this.defs.get(s);
    } else if (this.parent) {
      return this.parent.getDef(s);
    } else {
      return undefined;
    }
  }

  newDef(s: string, DefNode: DefNode): boolean {
    // REMARK: YOU ARE NOT ALLOWED TO DECLARE A FACT TWICE AT THE SAME ENV.
    if (this.getDef(s) !== undefined) {
      this.newMessage(
        `${s} already declared in this environment or its parents environments.`
      );
      return false;
    }

    this.defs.set(s, DefNode);
    this.newMessage(`[def] ${DefNode}`);
    return true;
  }

  // Return the lowest level of environment in which an operator with given name is declared.
  public whereIsOptDeclared(s: string): number | undefined {
    if (this.defs.get(s)) return 0;

    let curEnv: L_Env | undefined = this.parent;
    let n = 1;

    while (curEnv && curEnv.defs.get(s) === undefined) {
      n++;
      curEnv = curEnv.parent;
    }

    return curEnv?.defs.get(s) ? n : undefined;
  }

  newSingletonVar(fix: string): boolean {
    // TO MAKE MY LIFE EASIER SO THAT I DO NOT NEED TO BIND ENV TO VARIABLE, I forbid redefining a variable with the same name with any visible variable.
    if (this.varDeclared(fix)) {
      this.newMessage(`${fix} already declared.`);
      return false;
    }
    this.declaredVars.add(fix);
    return true;
  }

  varDeclaredAtCurrentEnv(key: string) {
    return this.declaredVars.has(key);
  }

  varDeclared(key: string): boolean {
    if (this.declaredVars.has(key)) {
      return true;
    } else {
      if (!this.parent) return false;
      else return this.parent.varDeclared(key);
    }
  }

  optDeclared(key: string): boolean {
    if (this.defs.get(key)) {
      return true;
    } else {
      if (!this.parent) return false;
      else return this.parent.optDeclared(key);
    }
  }

  getMessages() {
    return this.messages;
  }

  newMessage(s: string) {
    this.messages.push(s);
  }

  printClearMessage() {
    this.messages.forEach((m) => console.log(m));
    this.messages = [];
  }

  clearMessages() {
    this.messages = [];
  }

  OKMesReturnL_Out(message: L_Node | string): L_Out {
    if (message instanceof L_Node) this.newMessage(`OK! ${message}`);
    else this.newMessage(message);
    return L_Out.True;
  }

  OKMesReturnBoolean(message: L_Node | string): boolean {
    if (message instanceof L_Node) this.newMessage(`OK! ${message}`);
    else this.newMessage(message);
    return true;
  }

  errMesReturnL_Out(s: L_Node | string): L_Out {
    this.newMessage(`Error: ${s}`);
    return L_Out.Error;
  }

  errMesReturnBoolean(s: L_Node | string): boolean {
    this.newMessage(`Error: ${s}`);
    return false;
  }

  printDeclFacts() {
    console.log("\n--Declared Facts--\n");

    for (const [name, declFact] of this.defs) {
      console.log(name);
      console.log(declFact);
    }
  }

  getParent() {
    return this.parent;
  }

  toJSON() {
    return {
      vars: Array.from(this.declaredVars),
      defs: Object.fromEntries(this.defs),
      knowns: Object.fromEntries(this.knownFacts),
      macros: this.macros,
    };
  }

  // used by prove to check whether vars in factToCheck is redefined in block
  someVarsDeclaredHere(fact: ToCheckNode, freeVars: string[]): boolean {
    //*
    // if (fact instanceof OptNode) {
    //   const out = fact.vars.some(
    //     (e) => !freeVars.includes(e) && this.declaredVars.has(e)
    //   );
    //   return out;
    // } else if (fact instanceof LogicNode) {
    //   return (
    //     fact.onlyIfs.some((e) => this.someVarsDeclaredHere(e, fact.vars)) ||
    //     fact.req.some((e) => this.someVarsDeclaredHere(e, fact.vars))
    //   );
    // }
    //*

    throw Error();
  }

  // used by prove to check whether factToCheck is redefined in block
  someOptsDeclaredHere(fact: ToCheckNode): boolean {
    //*
    // if (fact instanceof OptNode) {
    //   return this.defs.get(fact.optSymbol) !== undefined;
    // } else if (fact instanceof LogicNode) {
    //   return (
    //     fact.onlyIfs.some((e) => this.someOptsDeclaredHere(e)) ||
    //     fact.req.some((e) => this.someOptsDeclaredHere(e))
    //   );
    // }
    //*

    throw Error();
  }

  optDeclaredHere(name: string): boolean {
    return this.defs.get(name) !== undefined;
  }
}
