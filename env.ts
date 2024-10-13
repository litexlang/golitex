import { isNull } from "lodash";
import {
  CallOptNode,
  DefNode,
  InferNode,
  L_Node,
  TNode,
  makeTemplateNodeFact,
} from "./ast";
import { L_Keywords, OptsConnectionSymbol } from "./common";
import {
  cErr_Out,
  cL_Out,
  fixOpt,
  freeFixMap,
  isL_OutErr,
  L_Out,
} from "./shared";

export type StoredFact = {
  vars: string[][];
  template: TNode[];
  requirements: CallOptNode[][]; // CallOptNode[] is related to a single Template
  onlyIfs: CallOptNode[]; // when this fact is satisfied, extra onlyIf is emitted
};

export class L_Env {
  errors: string[] = [];
  errorsWithDepth: [string, number][] = []; //? [error message, depth], number here does not work for the time being
  private errorDepth = 0;
  declaredVars: string[] = [];
  declaredTemplates: Map<string, TNode> = new Map<string, TNode>();
  father: L_Env | undefined;
  // symbolsFactsPairs: StoredFact[] = [];
  yaFacts: Map<string, CallOptNode[]> = new Map<string, CallOptNode[]>();

  constructor(father: L_Env | undefined = undefined) {
    this.father = father;
  }

  YANewFactEmit(opt: CallOptNode, emit: Boolean = true) {
    /** Much unnecessary info is stored here. e.g. The optName and optNameLst can be set to "" because the key of map already store that info. */
    if (this.yaFacts.has(opt.optName)) {
      this.yaFacts.get(opt.optName)?.push(opt);
    } else {
      this.yaFacts.set(opt.optName, [opt]);
    }

    if (emit) {
      opt.onlyIFs.forEach((e: CallOptNode) => this.YANewFactEmit(e, false));
    }
  }

  /**
   * whatever relT(opt).type is, checkEmit checks whether it's known true.
   */
  checkEmit(
    opt: CallOptNode,
    emit = true,
    emitTo: L_Env = this
  ): L_Out<Boolean> {
    const RFacts = this.yaFacts.get(opt.optName);
    if (!RFacts) {
      if (this.father === undefined) return cL_Out<Boolean>(false);
      else {
        // if current fact is checked true in its fatherEnv, emit in fatherEnv instead of son env.
        //? Maybe I should add a syntax to allow user to specify in which env the fact is emitted: the newEnv opened by prove or the global env.
        const out = this.father.checkEmit(opt, true);
        return out;
      }
    }

    /** Find all facts that the current input satisfies */
    const relT = this.relT(opt).v as TNode;
    let isT = false;
    for (const [i, singleFact] of (RFacts as CallOptNode[]).entries()) {
      if (!this._isLiterallyFact(singleFact.optParams, opt.optParams)) continue;

      const temp = freeFixMap(singleFact.optParams, opt.optParams);
      if (!temp.v) return cErr_Out(temp.err);
      const mapping = temp.v;

      /** Check requirements of this single fact */
      let facts: { name: string; params: string[][] }[] = singleFact.req.map(
        (e) => {
          return {
            name: e.optName,
            params: e.optParams.map((ls) =>
              ls.map((s) => {
                const res = mapping.get(s);
                if (res !== undefined)
                  return res; // replace hashVar in param list with fixed var
                else return s; // global var unspecified in parameter list
              })
            ),
          };
        }
      );

      isT = facts.every((e) =>
        this.checkEmit(CallOptNode.create(e.name, e.params), false)
      );

      if (!isT) continue;

      /** Emit onlyIfs (from opt and from relT)*/
      if (emit) {
        this.emit(singleFact, mapping, relT, emitTo);
      }
    }

    return isT ? cL_Out<Boolean>(true) : cL_Out<Boolean>(false);
  }

  private _isLiterallyFact(fact: string[][], arr2: string[][]) {
    return (
      fact.length === arr2.length &&
      fact.every(
        (row, i) =>
          row.length === arr2[i].length &&
          row.every((val, j) => val === arr2[i][j] || val.startsWith("#"))
      )
    );
  }

  //! 这里需要区分 infer, def 的emit标准
  emit(
    fact: CallOptNode,
    mapping: Map<string, string>,
    relT: TNode,
    emitTo: L_Env = this
  ) {
    // Requirements of InferNode must be checked
    if (relT instanceof InferNode) {
      const fixedRelTReq = fixOpt(
        this,
        fact,
        relT.getSelfFathersFreeVars(),
        relT.requirements
      );
      if (isNull(fixedRelTReq.v)) return;

      if (!fixedRelTReq.v.every((req) => this.checkEmit(req, false))) return;
    }

    // emit onlyIf from opt
    let facts = fact.onlyIFs.map((e) => {
      return CallOptNode.create(
        e.optName,
        e.optParams.map((ls) =>
          ls.map((s) => {
            const res = mapping.get(s);
            if (res !== undefined)
              return res; // replace free var in param list with fixed var
            else return s; // global var unspecified in parameter list
          })
        )
      );
    });
    facts.forEach((e) => emitTo.YANewFactEmit(e));

    // emit onlyIf from relT
    const fixedRelTOnlyIfs = fixOpt(
      this,
      fact,
      relT.getSelfFathersFreeVars(),
      relT.onlyIfExprs as CallOptNode[]
    );
    if (isNull(fixedRelTOnlyIfs.v)) return;
    else fixedRelTOnlyIfs.v.forEach((e) => emitTo.YANewFactEmit(e));
  }

  newVar(varName: string): boolean {
    if (this.declaredVars.includes(varName)) {
      return false;
    }

    if (L_Keywords.includes(varName)) {
      return false;
    }

    this.declaredVars.push(varName);
    return true;
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

  pushErrorMessage(s: string) {
    this.errors.push(s);
  }

  pushNewError(s: string, addDepth: Boolean = false) {
    if (addDepth) {
      this.errorDepth++;
    }
    this.errorsWithDepth.push([s, this.errorDepth]);
  }

  // Main function of the whole project
  // input full name of an opt, output the template of the lowest hierarchy
  getRelT(node: string | CallOptNode): TNode | undefined {
    const isTop = (s: string): boolean => {
      return !s.includes(OptsConnectionSymbol);
    };

    const getBeforeFirstColon = (str: string): string => {
      const colonIndex = str.indexOf(OptsConnectionSymbol);
      return colonIndex !== -1 ? str.slice(0, colonIndex) : str;
    };

    let s = "";
    if (node instanceof CallOptNode) s = node.optName;
    else s = node;

    let relT: TNode | undefined;

    const searchInCurrentEnv = (): TNode | undefined => {
      if (isTop(s)) {
        return this.declaredTemplates.get(s);
      } else {
        const topLevelTemplate = this.declaredTemplates.get(
          getBeforeFirstColon(s)
        );
        return topLevelTemplate?.getDeclaredSubTemplate(s);
      }
    };

    relT = searchInCurrentEnv();

    // If not found in current environment, search in father
    if (!relT && this.father) {
      relT = this.father.getRelT(node);

      return relT;
    } else {
      return relT;
    }
  }

  relT(node: string | CallOptNode): L_Out<TNode> {
    const isTop = (s: string): boolean => {
      return !s.includes(OptsConnectionSymbol);
    };

    const getBeforeFirstColon = (str: string): string => {
      const colonIndex = str.indexOf(OptsConnectionSymbol);
      return colonIndex !== -1 ? str.slice(0, colonIndex) : str;
    };

    let s = "";
    if (node instanceof CallOptNode) s = node.optName;
    else s = node;

    let relT: TNode | undefined;

    const searchInCurrentEnv = (): TNode | undefined => {
      if (isTop(s)) {
        return this.declaredTemplates.get(s);
      } else {
        const topLevelTemplate = this.declaredTemplates.get(
          getBeforeFirstColon(s)
        );
        return topLevelTemplate?.getDeclaredSubTemplate(s);
      }
    };

    relT = searchInCurrentEnv();

    // If not found in current environment, search in father
    if (!relT && this.father) {
      return this.father.relT(node);
    } else {
      if (relT === undefined) return cErr_Out(`${node.toString()} undeclared.`);
      return cL_Out(relT);
    }
  }

  printYAFacts() {
    console.log("\n-----facts-------\n");
    for (const fact of this.yaFacts) {
      console.log(fact);
    }
  }

  printDeclaredTemplates(doNotPrint: string[] = []) {
    console.log("\n-----template-----\n");

    for (const value of this.declaredTemplates) {
      if (doNotPrint.includes(value[0])) continue;
      console.log(value);
      console.log("");
    }
  }

  printErrorsWithDepth() {
    for (let i = this.errorsWithDepth.length - 1; i >= 0; i--) {
      let space = "";
      for (let j = 0; j < this.errorsWithDepth.length - 1 - i; j++) {
        space += "  ";
      }
      console.log(space + this.errorsWithDepth[i][0]);
    }
  }
}
