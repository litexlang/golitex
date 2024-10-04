import {
  CallOptNode,
  TemplateNode,
  makeTemplateNodeFact,
  TemplateNodeFact,
} from "./ast";
import { OptsConnectionSymbol } from "./common";
import {
  _paramsInOptAreDeclared,
  ExecInfo,
  execInfo,
  ResultType,
} from "./executor";

export class LiTeXEnv {
  errors: string[] = [];
  errorsWithDepth: [string, number][] = []; // [error message, depth]
  private errorDepth = 0;
  declaredVars: string[] = [];
  declaredTemplates: Map<string, TemplateNode> = new Map<
    string,
    TemplateNode
  >();
  father: LiTeXEnv | undefined;
  symbolsFactsPairs: {
    vars: string[][];
    template: TemplateNode[];
    requirements: CallOptNode[][];
  }[] = [];

  constructor(father: LiTeXEnv | undefined = undefined) {
    this.father = father;
  }

  newVar(varName: string): boolean {
    if (this.declaredVars.includes(varName)) {
      return false;
    }

    this.declaredVars.push(varName);
    return true;
  }

  symbolsFactsPairIsTrue(key: string[][], template: TemplateNode): boolean {
    for (let sfPair of this.symbolsFactsPairs) {
      if (!_isLiterallyFact(sfPair.vars, key)) {
        continue;
      } else {
        for (let templatesThatSatisfySFPair of sfPair.template) {
          // check whether we are manipulating the correct opt
          if (templatesThatSatisfySFPair.declOptName !== template.declOptName)
            continue;

          // no extra requirements
          if (sfPair.requirements.length === 0) {
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
              let tmp = this.getDeclaredTemplate(optName);
              if (!tmp) return false;
              let res = this.symbolsFactsPairIsTrue(fixedParams, tmp);
              if (!res) {
                allRequirementsSatisfied = false;
                break;
              }
            }
            if (!allRequirementsSatisfied) break;
          }

          if (allRequirementsSatisfied) return true;
          else continue;
        }
      }
    }

    if (this.father) return this.father.symbolsFactsPairIsTrue(key, template);
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

  // 在#时，这个函数有点问题,因为 #a, #b 会被当成不一样的东西，实际上他们是一样的
  newSymbolsFactsPair(
    key: string[][],
    template: TemplateNode,
    requirements: CallOptNode[][] = []
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

  pushCallOptFact(fact: CallOptNode): ExecInfo {
    const declaredTemplate = this.getDeclaredTemplate(fact.optName);
    if (!declaredTemplate)
      return execInfo(ResultType.Error, fact.optName + "has not been declared");
    declaredTemplate.newFact(this, makeTemplateNodeFact(fact.optParams));
    return execInfo(ResultType.KnowTrue);
  }

  // Main function of the whole project
  // input full name of an opt, output the template of the lowest hierarchy
  getDeclaredTemplate(node: string | CallOptNode): TemplateNode | undefined {
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

    let relatedTemplate: TemplateNode | undefined;

    const searchInCurrentEnv = (): TemplateNode | undefined => {
      if (isTop(s)) {
        return this.declaredTemplates.get(s);
      } else {
        const topLevelTemplate = this.declaredTemplates.get(
          getBeforeFirstColon(s)
        );
        return topLevelTemplate?.getDeclaredSubTemplate(s);
      }
    };

    relatedTemplate = searchInCurrentEnv();

    // If not found in current environment, search in father
    if (!relatedTemplate && this.father) {
      relatedTemplate = this.father.getDeclaredTemplate(node);

      return relatedTemplate;
    } else {
      return relatedTemplate;
    }
  }

  // getFact(s: string): TemplateNodeFact[] | undefined {
  //   const node = this.getDeclaredTemplate(s);
  //   return node?.facts;
  // }

  printCallOptFacts() {
    console.log("-----facts-------\n");
    for (const fact of this.symbolsFactsPairs) {
      console.log(fact);
    }

    // for (const template of this.declaredTemplates.values()) {
    //   printFact(template);
    // }
    // console.log("");

    // function printFact(template: TemplateNode, fatherName: string = "") {
    //   const name = fatherName + OptsConnectionSymbol + template.declOptName;
    //   console.log(name);
    //   console.log(template.facts.map((e) => e.params));
    //   for (const subTemplate of template.declaredTemplates.values()) {
    //     printFact(subTemplate, name);
    //   }
    // }
  }

  printDeclaredTemplates() {
    console.log("-----template-----\n");

    for (const value of this.declaredTemplates) {
      console.log(value);
      console.log("");
    }
  }
}
