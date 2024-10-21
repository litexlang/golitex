import { isNull, map } from "lodash";
import {
  // CallOptNode,
  DeclNode,
  // InferNode,
  ShortCallOptNode,
  // TNode,
  FactNode,
  IfThenNode,
  FactType,
} from "./ast";
import { L_Keywords, OptsConnectionSymbol } from "./common";

// export type StoredFact = {
//   vars: string[][];
//   template: TNode[];
//   requirements: CallOptNode[][]; // CallOptNode[] is related to a single Template
//   onlyIfs: CallOptNode[]; // when this fact is satisfied, extra onlyIf is emitted
// };

export class StoredFactValue {
  constructor(
    public vars: string[][],
    public req: FactNode[],
    public isT: Boolean = false
  ) {}

  toString() {
    let result = "";

    // Add vars part
    result += this.vars.map((subArray) => subArray.join(", ")).join("; ");

    // Add req part if it's not empty
    if (this.req.length > 0) {
      result += " | ";
      result += this.req.map((e) => e.toString()).join("; ");
    }

    // Add 'not' if isT is false
    if (!this.isT) {
      result = "(not) " + result;
    }

    return result;
  }
}

export class L_Env {
  messages: string[] = []; //? [error message, depth], number here does not work for the time being
  declaredVars: string[] = [];
  // declaredTemplates = new Map<string, TNode>();
  father: L_Env | undefined;
  // facts = new Map<string, CallOptNode[]>();
  bys = new Map<string, FactNode>();

  private shortOptFacts = new Map<string, StoredFactValue[]>();
  factTypes = new Map<string, FactType>();

  // private declTemps = new Map<string, DeclNode>();

  constructor(father: L_Env | undefined = undefined) {
    this.father = father;
  }

  getOptType(s: string) {
    let out = this.factTypes.get(s);
    if (!out) {
      return this.father?.factTypes.get(s);
    } else return out;
  }

  getShortOptFact(s: string): StoredFactValue[] | undefined {
    let out = this.shortOptFacts.get(s);
    return out ? out : this.father?.getShortOptFact(s);
  }

  /**
   * @param hash stores which given vars are onlyIf vars
   */
  addShortOptFact(opt: ShortCallOptNode, req: FactNode[]) {
    if (this.shortOptFacts.get(opt.fullName) === undefined) {
      this.shortOptFacts.set(opt.fullName, [
        new StoredFactValue(opt.params, req, opt.isT),
      ]);
    } else {
      this.shortOptFacts
        .get(opt.fullName)!
        .push(new StoredFactValue(opt.params, req, opt.isT));
    }
  }

  declareNewVar(v: string | string[]): Boolean {
    if (Array.isArray(v)) {
      for (let i = 0; i < v.length; i++) {
        if (!this.varsAreNotDeclared(v[i])) return false;
      }
      this.declaredVars.concat(v);
      return true;
    } else {
      if (this.varsAreNotDeclared(v)) {
        this.declaredVars.push(v);
        return true;
      } else return false;
    }
  }

  varsAreNotDeclared(vars: string[] | string): boolean {
    const isVarDeclared = (v: string): boolean => {
      if (this.declaredVars.includes(v) || v.startsWith("#")) {
        return true;
      }
      return this.father ? this.father.isVarDeclared(v) : false;
    };

    if (Array.isArray(vars)) {
      return vars.every((v) => !isVarDeclared(v));
    } else {
      return !isVarDeclared(vars);
    }
  }

  private isVarDeclared(v: string): boolean {
    if (this.declaredVars.includes(v) || v.startsWith("#")) {
      return true;
    }
    return this.father ? this.father.isVarDeclared(v) : false;
  }

  newMessage(s: string) {
    this.messages.push(s);
  }

  printFacts() {
    console.log("\n-----facts-------\n");

    for (const [key, factUnderCurKey] of this.shortOptFacts) {
      const t = this.factTypes.get(key);
      let tStr = "";
      if (t === FactType.Def) {
        tStr = "def";
      } else if (t === FactType.IfThen) {
        tStr = "if-then";
      } else if (t === FactType.Or) {
        tStr = "or";
      }

      console.log(`[${tStr}] ${key}`);
      factUnderCurKey.forEach((e: StoredFactValue) => {
        console.log(e.toString());
      });
      console.log();
    }
  }

  // newFactEmit(opt: CallOptNode, emit: Boolean = true) {
  //   /** Much unnecessary info is stored here. e.g. The optName and optNameLst can be set to "" because the key of map already store that info. */
  //   if (this.facts.has(opt.optName)) {
  //     if (opt.onlyIFs.length === 0 && this.checkEmit(opt, false)) return;
  //     else this.facts.get(opt.optName)?.push(opt);
  //   } else {
  //     this.facts.set(opt.optName, [opt]);
  //   }

  //   if (emit) {
  //     opt.onlyIFs.forEach((e: CallOptNode) => this.newFactEmit(e, false));
  //   }
  // }

  // getSelfFathersFact(opt: CallOptNode): CallOptNode[] {
  //   const out: CallOptNode[] = [];
  //   let currentEnv: L_Env | undefined = this;
  //   while (currentEnv !== undefined) {
  //     const RFacts = currentEnv.facts.get(opt.optName);
  //     if (notUdf(RFacts)) RFacts?.forEach((e) => out.push(e));
  //     currentEnv = (currentEnv as L_Env).father;
  //   }
  //   return out;
  // }

  /**
   * whatever relT(opt).type is, checkEmit checks whether it's known true.
   */
  // checkEmit(
  //   opt: CallOptNode,
  //   emit: Boolean = true,
  //   emitTo: L_Env = this
  // ): L_Out<Boolean> {
  //   const RFacts = this.getSelfFathersFact(opt);
  //   if (RFacts.length === 0) return cL_Out<Boolean>(false);

  //   /** Find all facts that the current input satisfies */
  //   const relT = this.relT(opt).v as TNode;
  //   let isT = false;
  //   for (const [i, singleFact] of RFacts.entries()) {
  //     const mapping = this.useSingleFreeFactToCheck(singleFact, opt);
  //     if (mapping === undefined) continue;
  //     else isT = true;

  //     /** Emit onlyIfs (from opt and from relT)*/
  //     // ! I think this piece of code should be refactored by relT.emit
  //     if (emit) {
  //       this.emitByMapping(singleFact, mapping, relT, emitTo);
  //     }
  //   }

  //   return isT ? cL_Out<Boolean>(true) : cL_Out<Boolean>(false);
  // }

  // useSingleFreeFactToCheck(
  //   freeFact: CallOptNode,
  //   opt: CallOptNode
  // ): Map<string, string> | UdfErr {
  //   if (!this._isLiterallyFact(freeFact.optParams, opt.optParams))
  //     return undefined;

  //   const temp = freeFixMap(freeFact.optParams, opt.optParams);
  //   if (!temp.v) return undefined;
  //   const mapping = temp.v;

  //   /**
  //    * Check requirements of this single fact
  //    * NOTICE LITERALLY CORRECT IS NOT ENOUGH, OPT MUST SATISFIED EXTRA
  //    * ONLYIFs BOUND TO THIS STORED FACT.
  //    */
  //   let facts: { name: string; params: string[][] }[] = freeFact.req.map(
  //     (e) => {
  //       return {
  //         name: e.optName,
  //         params: e.optParams.map((ls) =>
  //           ls.map((s) => {
  //             const res = mapping.get(s);
  //             if (res !== undefined)
  //               return res; // replace hashVar in param list with fixed var
  //             else return s; // global var unspecified in parameter list
  //           })
  //         ),
  //       };
  //     }
  //   );

  //   if (
  //     facts.every(
  //       (e) => this.checkEmit(CallOptNode.create(e.name, e.params), false).v
  //     )
  //   ) {
  //     return mapping;
  //   } else return undefined;
  // }

  // private _isLiterallyFact(fact: string[][], arr2: string[][]) {
  //   return (
  //     fact.length === arr2.length &&
  //     fact.every(
  //       (row, i) =>
  //         row.length === arr2[i].length &&
  //         row.every((val, j) => val === arr2[i][j] || val.startsWith("#"))
  //     )
  //   );
  // }

  // // ! I think this piece of code should be refactored by relT.emit
  // emitByMapping(
  //   fact: CallOptNode,
  //   mapping: Map<string, string>,
  //   relT: TNode,
  //   emitTo: L_Env = this
  // ) {
  //   // Requirements of InferNode must be checked
  //   if (relT instanceof InferNode) {
  //     const fixedRelTReq = fixOpt(
  //       this,
  //       fact,
  //       relT.allVars(),
  //       relT.requirements
  //     );
  //     if (isNull(fixedRelTReq.v)) return;

  //     if (!fixedRelTReq.v.every((req) => this.checkEmit(req, false))) return;
  //   }

  //   // emit onlyIf from opt
  //   let facts = fact.onlyIFs.map((e) => {
  //     return CallOptNode.create(
  //       e.optName,
  //       e.optParams.map((ls) =>
  //         ls.map((s) => {
  //           const res = mapping.get(s);
  //           if (res !== undefined)
  //             return res; // replace free var in param list with fixed var
  //           else return s; // global var unspecified in parameter list
  //         })
  //       )
  //     );
  //   });
  //   facts.forEach((e) => emitTo.newFactEmit(e));

  //   // emit onlyIf from relT
  //   const fixedRelTOnlyIfs = fixOpt(
  //     this,
  //     fact,
  //     relT.allVars(),
  //     relT.onlyIfs as CallOptNode[]
  //   );
  //   if (isNull(fixedRelTOnlyIfs.v)) return;
  //   else fixedRelTOnlyIfs.v.forEach((e) => emitTo.newFactEmit(e));
  // }

  // optDecled(name: string) {
  //   let out = this.factTypes.has(name);
  //   if (!out) {
  //     return this.father?.factTypes.get(s);
  //   } else return
  // }

  // If opt is not declared, just throw error. I no longer need to write `if (... !== undefined)`
  // declTemp(name: string, fact: DeclNode) {
  //   if (this.declTemps.has(name)) throw Error(`${name} is already declared`);
  //   else {
  //     this.declTemps.set(name, fact);
  //   }
  // }

  // getDeclTemp(name: string): DeclNode | undefined {
  //   const out = this.declTemps.get(name);
  //   return out;
  // }

  // Main function of the whole project
  // input full name of an opt, output the template of the lowest hierarchy
  // getRelT(node: string | CallOptNode): TNode | undefined {
  //   const isTop = (s: string): boolean => {
  //     return !s.includes(OptsConnectionSymbol);
  //   };

  //   const getBeforeFirstColon = (str: string): string => {
  //     const colonIndex = str.indexOf(OptsConnectionSymbol);
  //     return colonIndex !== -1 ? str.slice(0, colonIndex) : str;
  //   };

  //   let s = "";
  //   if (node instanceof CallOptNode) s = node.optName;
  //   else s = node;

  //   let relT: TNode | undefined;

  //   const searchInCurrentEnv = (): TNode | undefined => {
  //     if (isTop(s)) {
  //       return this.declaredTemplates.get(s);
  //     } else {
  //       const topLevelTemplate = this.declaredTemplates.get(
  //         getBeforeFirstColon(s)
  //       );
  //       return topLevelTemplate?.getDeclaredSubTemplate(s);
  //     }
  //   };

  //   relT = searchInCurrentEnv();

  //   // If not found in current environment, search in father
  //   if (!relT && this.father) {
  //     relT = this.father.getRelT(node);

  //     return relT;
  //   } else {
  //     return relT;
  //   }
  // }

  // relT(node: string | CallOptNode): L_Out<TNode> {
  //   const isTop = (s: string): boolean => {
  //     return !s.includes(OptsConnectionSymbol);
  //   };

  //   const getBeforeFirstColon = (str: string): string => {
  //     const colonIndex = str.indexOf(OptsConnectionSymbol);
  //     return colonIndex !== -1 ? str.slice(0, colonIndex) : str;
  //   };

  //   let s = "";
  //   if (node instanceof CallOptNode) s = node.optName;
  //   else s = node;

  //   let relT: TNode | undefined;

  //   const searchInCurrentEnv = (): TNode | undefined => {
  //     if (isTop(s)) {
  //       return this.declaredTemplates.get(s);
  //     } else {
  //       const topLevelTemplate = this.declaredTemplates.get(
  //         getBeforeFirstColon(s)
  //       );
  //       return topLevelTemplate?.getDeclaredSubTemplate(s);
  //     }
  //   };

  //   relT = searchInCurrentEnv();

  //   // If not found in current environment, search in father
  //   if (!relT && this.father) {
  //     return this.father.relT(node);
  //   } else {
  //     if (relT === undefined) return cErr_Out(`${node.toString()} undeclared.`);
  //     return cL_Out(relT);
  //   }
  // }

  // printDeclaredTemplates(doNotPrint: string[] = []) {
  // console.log("\n-----template-----\n");
  // for (const [key, tNode] of this.declTemps) {
  //   if (doNotPrint.includes(key)) continue;
  //   console.log(tNode);
  //   // printTAndSubT(tNode);
  // }
  // function printTAndSubT(tNode: DeclNode) {
  //   console.log(tNode.toString() + "\n");
  //   for (const subTNode of tNode.declaredTemplates) {
  //     printTAndSubT(subTNode[1]);
  //   }
  // }
  // }
}
