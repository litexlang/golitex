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
  declaredVars: string[] = [];
  declaredTemplates: Map<string, TemplateNode> = new Map<
    string,
    TemplateNode
  >();
  father: LiTeXEnv | undefined;
  symbolsFactsPairs: Map<string[][], TemplateNode> = new Map<
    string[][],
    TemplateNode
  >();

  constructor(father: LiTeXEnv | undefined = undefined) {
    this.father = father;
  }

  newSymbolsFactsPair(key: string[][], template: TemplateNode) {
    this.symbolsFactsPairs.set(key, template);
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

  getFact(s: string): TemplateNodeFact[] | undefined {
    const node = this.getDeclaredTemplate(s);
    return node?.facts;
  }

  printCallOptFacts() {
    console.log("-----facts-------\n");
    for (const template of this.declaredTemplates.values()) {
      printFact(template);
    }
    console.log("");

    function printFact(template: TemplateNode, fatherName: string = "") {
      const name = fatherName + OptsConnectionSymbol + template.declOptName;
      console.log(name);
      console.log(template.facts.map((e) => e.params));
      for (const subTemplate of template.declaredTemplates.values()) {
        printFact(subTemplate, name);
      }
    }
  }

  printDeclaredTemplates() {
    console.log("-----template-----\n");

    for (const value of this.declaredTemplates) {
      console.log(value);
      console.log("");
    }
  }
}
