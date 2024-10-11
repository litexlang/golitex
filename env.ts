import { CallOptNode, TNode, makeTemplateNodeFact } from "./ast";
import { L_Keywords, OptsConnectionSymbol } from "./common";
import { emitFree, hNoRelTErr, hRunErr, RType } from "./executor";
import { cErr_Out, cL_Out, freeFixMap, L_Out } from "./shared";

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
  symbolsFactsPairs: StoredFact[] = [];
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

  // YANewFactEmit(
  //   TName: string,
  //   vars: string[][],
  //   req: CallOptNode[] = [],
  //   onlyIf: CallOptNode[] = []
  // ) {
  //   if (this.yaFacts.has(TName)) {
  //     this.yaFacts
  //       .get(TName)
  //       ?.push(CallOptNode.create("", vars, [req], onlyIf));
  //   } else {
  //     this.yaFacts.set(TName, [CallOptNode.create("", vars, [req], onlyIf)]);
  //   }
  // }

  yaDefCheckEmit(opt: CallOptNode): L_Out<Boolean> {
    // const RelT = this.getRelT(opt);
    // if (!RelT) {
    //   hNoRelTErr(opt);
    //   return cL_Out<Boolean>(false);
    // }
    const RFacts = this.yaFacts.get(opt.optName);
    if (!RFacts) return cL_Out<Boolean>(false);

    /** Find all facts that the current input satisfies */
    let isT = false;
    for (const [i, singleFact] of (RFacts as CallOptNode[]).entries()) {
      if (!_isLiterallyFact(singleFact.optParams, opt.optParams)) continue;

      const temp = freeFixMap(singleFact.optParams, opt.optParams);
      if (!temp.value) return cErr_Out(temp.errStr);
      const mapping = temp.value;

      /** Check requirements of this single fact */
      let facts: { name: string; params: string[][] }[] = singleFact.req.map(
        (e) => {
          return {
            name: e.optName,
            params: e.optParams.map((ls) =>
              ls.map((s) => {
                const res = mapping.get(s);
                if (res !== undefined)
                  return res; // replace free var in param list with fixed var
                else return s; // global var unspecified in parameter list
              })
            ),
          };
        }
      );

      isT = facts.every((e) =>
        this.yaDefCheckEmit(CallOptNode.create(e.name, e.params))
      );

      if (!isT) continue;

      /** Emit onlyIfs */
      facts = singleFact.onlyIFs.map((e) => {
        return {
          name: e.optName,
          params: e.optParams.map((ls) =>
            ls.map((s) => {
              const res = mapping.get(s);
              if (res !== undefined)
                return res; // replace free var in param list with fixed var
              else return s; // global var unspecified in parameter list
            })
          ),
        };
      });
      facts.forEach((e) =>
        this.YANewFactEmit(CallOptNode.create(e.name, e.params))
      );
    }
    return isT ? cL_Out<Boolean>(true) : cL_Out<Boolean>(false);

    function _isLiterallyFact(fact: string[][], arr2: string[][]) {
      return (
        fact.length === arr2.length &&
        fact.every(
          (row, i) =>
            row.length === arr2[i].length &&
            row.every((val, j) => val === arr2[i][j] || val.startsWith("#"))
        )
      );
    }
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

  isCallOptTrue(opt: CallOptNode): Boolean {
    const relatedT = this.getRelT(opt);
    if (!relatedT) {
      hRunErr(this, RType.Unknown);
      return false;
    } else {
      return this.isStoredTrueFact(opt.optParams, relatedT, opt);
    }
  }

  isFact(TName: string, params: string[][]): Boolean {
    const relT = this.getRelT(TName);
    if (!relT) {
      hNoRelTErr(TName);
      return false;
    } else {
      return this.isStoredTrueFact(params, relT);
    }
  }

  isStoredTrueFact(
    key: string[][],
    template: TNode,
    //! 这种emit方式有问题：如果我有多个fact都能证明这个东西是对的，那么只有一个storedFact onlyif 会被释放
    callOpt: undefined | CallOptNode = undefined // when defined, something will be emitted: the storedFact
  ): boolean {
    for (let sfPair of this.symbolsFactsPairs as StoredFact[]) {
      if (!_isLiterallyFact(sfPair.vars, key)) {
        continue;
      } else {
        for (let templatesThatSatisfySFPair of sfPair.template) {
          // check whether we are manipulating the correct opt
          if (templatesThatSatisfySFPair.name !== template.name) continue;

          // no extra requirements
          if (sfPair.requirements.length === 0) {
            if (callOpt)
              emitFree(this, callOpt, template, false, false, sfPair.onlyIfs);

            return true;
          }

          // check extra requirements
          // mapping: from free(those #xxx are "free") to fixed
          let sfPairVarToFixVarMapping = new Map<string, string>();
          sfPair.vars.forEach((e, i) =>
            e.forEach((s, j) => sfPairVarToFixVarMapping.set(s, key[i][j]))
          );

          let allRequirementsSatisfied = true;
          for (let rl of sfPair.requirements) {
            for (let req of rl) {
              // check whether each requirement is satisfied
              const optName: string = req.optName; // req name
              let fixedParams: string[][] = [];

              // req.optParams are free. fix them. put them into fixedParams
              for (let i = 0; i < req.optParams.length; i++) {
                fixedParams.push([]);
                for (let j = 0; j < req.optParams[i].length; j++) {
                  let s = sfPairVarToFixVarMapping.get(req.optParams[i][j]);
                  if (!s) return false;
                  fixedParams[i].push(s as string);
                }
              }

              // check fixed params
              let tmp = this.getRelT(optName);
              if (!tmp) return false;
              let res = this.isStoredTrueFact(fixedParams, tmp); // nothing is emitted here.
              if (!res) {
                allRequirementsSatisfied = false;
                break;
              }
            }
            if (!allRequirementsSatisfied) break;
          }

          if (allRequirementsSatisfied) {
            if (callOpt)
              emitFree(this, callOpt, template, false, false, sfPair.onlyIfs);
            return true;
          } else continue;
        }
      }
    }

    if (this.father)
      return this.father.isStoredTrueFact(key, template, callOpt);
    else return false;

    function _isLiterallyFact(arr1: string[][], arr2: string[][]): boolean {
      if (arr1.length !== arr2.length) return false;

      for (let i = 0; i < arr1.length; i++) {
        if (arr1[i].length !== arr2[i].length) return false;
        for (let j = 0; j < arr1[i].length; j++) {
          const val1 = arr1[i][j];
          const val2 = arr2[i][j];
          // if the vars stored in env.symbolsFactsPair start with # then is right.
          if (val1 !== val2 && !val1.startsWith("#")) {
            return false;
          }
        }
      }

      return true;
    }
  }

  private arraysEqual(arr1: string[][], arr2: string[][]): boolean {
    if (arr1.length !== arr2.length) return false;

    for (let i = 0; i < arr1.length; i++) {
      if (arr1[i].length !== arr2[i].length) return false;
      for (let j = 0; j < arr1[i].length; j++) {
        if (arr1[i][j] !== arr2[i][j]) return false;
      }
    }

    return true;
  }

  newCallOptFact(opt: CallOptNode): Boolean {
    const T = this.getRelT(opt);
    if (!T) {
      hRunErr(this, RType.Error, `${opt.optName} is not declared`);
      return false;
    } else {
      this.newStoredFact(opt.optParams, T);
      return true;
    }
  }

  newStoredFact(
    key: string[][],
    template: TNode,
    requirements: CallOptNode[][] = [],
    onlyIfs: CallOptNode[] = []
  ) {
    const existingPair = this.symbolsFactsPairs.find((pair) =>
      this.arraysEqual(pair.vars, key)
    );

    if (existingPair) {
      existingPair.template.push(template);
    } else {
      this.symbolsFactsPairs.push({
        vars: key,
        template: [template],
        requirements: requirements,
        onlyIfs: onlyIfs,
      });
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

  pushErrorMessage(s: string) {
    this.errors.push(s);
  }

  pushNewError(s: string, addDepth: Boolean = false) {
    if (addDepth) {
      this.errorDepth++;
    }
    this.errorsWithDepth.push([s, this.errorDepth]);
  }

  // pushCallOptFact(fact: CallOptNode): RInfo {
  //   const declaredTemplate = this.getRelT(fact.optName);
  //   if (!declaredTemplate)
  //     return hInfo(RType.Error, fact.optName + "has not been declared");
  //   declaredTemplate.newFact(this, makeTemplateNodeFact(fact.optParams));
  //   return hInfo(RType.KnowTrue);
  // }

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

  // getFact(s: string): TNodeFact[] | undefined {
  //   const node = this.getRelT(s);
  //   return node?.facts;
  // }

  printYAFacts() {
    console.log("\n-----facts-------\n");
    for (const fact of this.yaFacts) {
      console.log(fact);
    }
  }

  printCallOptFacts() {
    console.log("\n-----facts-------\n");
    for (const fact of this.symbolsFactsPairs) {
      console.log(fact);
    }

    // for (const template of this.declaredTemplates.values()) {
    //   printFact(template);
    // }
    // console.log("");

    // function printFact(template: TNode, fatherName: string = "") {
    //   const name = fatherName + OptsConnectionSymbol + template. name;
    //   console.log(name);
    //   console.log(template.facts.map((e) => e.params));
    //   for (const subTemplate of template.declaredTemplates.values()) {
    //     printFact(subTemplate, name);
    //   }
    // }
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
