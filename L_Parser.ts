import {
  LogicNode,
  L_FactNode,
  OptFactNode,
  FormulaSubNode,
  FactsNode,
  OrToCheckNode,
  AndToCheckNode,
  IsConceptNode,
  BuiltinCheckNode,
  IsFormNode,
  IfNode,
  IfVarsFormReqType,
} from "./L_Facts";
import { L_Node } from "./L_Nodes";
import * as L_Nodes from "./L_Nodes";
import { L_Env } from "./L_Env";
import { builtinFactNames, L_KW } from "./L_Keywords";
import * as L_Structs from "./L_Structs";
import {
  L_Singleton,
  L_Composite,
  L_Symbol,
  L_UndefinedSymbol,
  IndexedSymbol,
} from "./L_Symbols";
import { messageParsingError } from "./L_Report";
import * as L_Report from "./L_Report";
import { tryNewFact } from "./L_Memory";
import { checkFact } from "./L_Checker";
import * as L_Memory from "./L_Memory";
import { L_Tokens } from "./L_Lexer";
import { FactVarsDeclaredChecker } from "./L_Facts";
import { SymbolDeclaredChecker } from "./L_Symbols";

// The reason why the returned valued is L_Node[] is that when checking, there might be a list of facts.
export function parseSingleNode(env: L_Env, tokens: L_Tokens): L_Node | null {
  const skipper = new Skipper(env, tokens);
  try {
    if (tokens.isEnd()) return null;

    if (isCurToken(tokens, L_KW.L_End)) {
      skipper.skip();
      while (!tokens.isEnd() && isCurToken(tokens, L_KW.L_End)) {
        skipper.skip();
      }
      if (tokens.isEnd()) return null;
    }

    if (tokens.isEnd()) {
      return null;
    }

    switch (tokens.peek()) {
      case L_KW.LCurlyBrace:
        return localEnvParse(env, tokens);
      case L_KW.Prove:
      case L_KW.ProveByContradiction:
        return proveParse(env, tokens);
    }

    switch (tokens.peek()) {
      case L_KW.Know:
        return knowParse(env, tokens);
      case L_KW.Let:
        return letParse(env, tokens);
      case L_KW.DefConcept:
        return defConceptParse(env, tokens);
      case L_KW.DefOperator:
        return defOperatorParse(env, tokens);
      case L_KW.Lets:
        return letsParse(env, tokens);
      case L_KW.Include:
        return includeParse(env, tokens);
      case L_KW.DefLiteralOperator:
        return defLiteralOperatorParse(env, tokens);
      // case L_KW.LetFormal:
      //   if (letFormalParse(env, tokens) === L_Out.True) return ;
      case L_KW.LetAlias:
        return letAliasParse(env, tokens);
      case L_KW.Have:
        // TODO: vars declared
        return haveParse(env, tokens);
      case L_KW.ConceptAlias:
        return conceptAliasParse(env, tokens);
    }

    const fact = factParse(env, tokens);
    skipper.skip(L_KW.L_End);
    return fact;
  } catch (error) {
    if (error instanceof Error) env.report(error.message);
    env.report(
      `error at ${tokens.curTokIndex()} -- ${tokens.sc.slice(
        skipper.start,
        tokens.curTokIndex()
      )}`
    );
    throw error;
  }
}

function arrParse<T>(
  env: L_Env,
  tokens: L_Tokens,
  parseFunc: Function,
  end: string[] | string
): T[] {
  const skipper = new Skipper(env, tokens);

  try {
    const out: T[] = [];
    while (!isCurToken(tokens, end)) {
      out.push(parseFunc(env, tokens));
      if (isCurToken(tokens, ",")) skipper.skip(",");
    }

    return out;
  } catch (error) {
    messageParsingError(arrParse, error);
    throw error;
  }
}

function optSymbolParse(env: L_Env, tokens: L_Tokens): L_Structs.OptSymbol {
  const skipper = new Skipper(env, tokens);

  try {
    if (tokens.peek() === L_KW.FreeConceptPrefix) {
      skipper.skip(L_KW.FreeConceptPrefix);
      const name = skipper.skip();
      return new L_Structs.FreeOptSymbol(name);
    } else {
      const name = skipper.skip();
      return new L_Structs.OptSymbol(name);
    }
  } catch (error) {
    messageParsingError(optSymbolParse, error);
    throw error;
  }
}

// function compositeParse(env: L_Env, tokens: L_Tokens): L_Composite {
//   const skipper = new Skipper(env, tokens);

//   try {
//     skipper.skip(L_KW.Slash);
//     const name = skipper.skip();
//     skipper.skip("{");
//     const values: L_Symbol[] = [];
//     while (!isCurToken(tokens, "}")) {
//       values.push(SymbolParser.symbolParse(env, tokens));
//       if (isCurToken(tokens, ",")) skipper.skip(",");
//     }
//     skipper.skip("}");
//     return new L_Composite(name, values);
//   } catch (error) {
//     messageParsingError(compositeParse, error);
//     throw error;
//   }
// }

export class Skipper {
  curTokens: string[] = [];
  tokens: L_Tokens;
  start: number;

  constructor(env: L_Env, tokens: L_Tokens) {
    this.tokens = tokens;
    this.start = tokens.curTokIndex();
  }

  nodeString(): string {
    return this.tokens.sc.slice(this.start, this.tokens.curTokIndex());
  }

  skip(s: string | string[] = ""): string {
    try {
      if (typeof s === "string") {
        if (s === "") {
          const out = this.tokens.shift();
          if (out === undefined) throw Error(`There is no more token.`);
          this.curTokens.push(out);
          return out;
        } else if (s === this.tokens.peek()) {
          const out = this.tokens.shift();
          if (out === undefined) throw Error(`There is no more token.`);
          this.curTokens.push(out);
          return out;
        } else {
          // env.report("unexpected symbol: " + this.tokens.peek());
          throw Error("unexpected symbol: " + this.tokens.peek());
        }
      } else {
        for (const value of s) {
          if (value === this.tokens.peek()) {
            const out = this.tokens.shift();
            if (out === undefined) throw Error;
            this.curTokens.push(out);
            return out;
          }
        }
        // env.report("unexpected symbol: " + this.tokens.peek());
        throw Error("unexpected symbol: " + this.tokens.peek());
      }
    } catch (error) {
      throw Error();
    }
  }
}

// used in regex parser
function skipString(tokens: L_Tokens): string {
  try {
    if (tokens.peek() === '"') tokens.shift();
    else throw Error();
    let out = "";
    while (!isCurToken(tokens, '"')) {
      out += tokens.peek();
      tokens.shift();
    }
    if (tokens.peek() === '"') tokens.shift();
    else throw Error();
    return out;
  } catch (error) {
    throw Error();
  }
}

function isCurToken(tokens: L_Tokens, str: string | string[]) {
  if (!Array.isArray(str)) {
    return str === tokens.peek();
  } else {
    return str.includes(tokens.peek());
  }
}

// @end: when parsing local env, } is the end; when parsing source code, node is the end
export function parseNodes(
  env: L_Env,
  tokens: L_Tokens,
  end: string | null
): L_Structs.ParsedNode[] {
  const skipper = new Skipper(env, tokens);

  try {
    const out: L_Structs.ParsedNode[] = [];

    if (end === null) {
      while (!tokens.isEnd()) {
        const node = parseSingleNode(env, tokens);
        if (node !== null)
          out.push(new L_Structs.ParsedNode(node, skipper.nodeString()));
      }
    } else {
      while (tokens.peek() !== end) {
        const node = parseSingleNode(env, tokens);
        if (node !== null)
          out.push(new L_Structs.ParsedNode(node, skipper.nodeString()));
      }
    }

    return out;
  } catch (error) {
    env.report(`Error: Parsing Error.`);
    throw error;
  }
}

function knowParse(env: L_Env, tokens: L_Tokens): null {
  const skipper = new Skipper(env, tokens);

  try {
    skipper.skip(L_KW.Know);
    const names: string[] = [];
    let facts = parseFactsArrCheckVarsDeclFixIfPrefix(env, tokens, [
      L_KW.L_End,
    ]);
    skipper.skip(L_KW.L_End);
    const out = new L_Nodes.KnowNode(facts, names);
    return knowExec(env, out);
  } catch (error) {
    messageParsingError(knowParse, error);
    throw error;
  }

  function knowExec(env: L_Env, node: L_Nodes.KnowNode): null {
    try {
      node.facts.forEach((e) => env.tryFactDeclaredOrBuiltin(e));

      for (const onlyIf of node.facts) {
        L_Memory.tryNewFact(env, onlyIf);
      }

      return null;
    } catch (error) {
      L_Report.L_ReportErr(env, knowExec, node);
      throw error;
    }
  }
}

function letParse(env: L_Env, tokens: L_Tokens): null {
  const skipper = new Skipper(env, tokens);

  try {
    skipper.skip(L_KW.Let);

    const vars: string[] = [];
    while (![L_KW.L_End, , ":"].includes(tokens.peek())) {
      vars.push(skipper.skip());
      if (isCurToken(tokens, ",")) skipper.skip(",");
    }

    if (vars.some((e) => Object.keys(L_KW).includes(e) || e.startsWith("\\"))) {
      env.report(`Error: ${vars} contain LiTeX keywords.`);
      throw Error();
    }

    let out: L_Nodes.LetNode | undefined = undefined;

    if (isCurToken(tokens, L_KW.L_End)) {
      skipper.skip(L_KW.L_End);
      out = new L_Nodes.LetNode(vars, []);
    } else {
      skipper.skip(":");
      const facts = parseFactsArrCheckVarsDeclFixIfPrefix(
        env,
        tokens,
        [L_KW.L_End],
        vars.map((e) => new L_Singleton(e))
      );
      skipper.skip(L_KW.L_End);
      out = new L_Nodes.LetNode(vars, facts);
    }

    return letExec(env, out);
  } catch (error) {
    messageParsingError(letParse, error);
    throw error;
  }

  function letExec(env: L_Env, node: L_Nodes.LetNode): null {
    try {
      for (const e of node.vars) {
        env.tryNewPureSingleton(e);
      }

      node.facts.forEach((e) => env.tryFactDeclaredOrBuiltin(e));

      // store new facts
      for (const onlyIf of node.facts) {
        L_Memory.tryNewFact(env, onlyIf);
      }

      env.report(`[let] ${node}`);
      return null;
    } catch (error) {
      L_Report.L_ReportErr(env, letExec, node);
      throw error;
    }
  }
}

function proveParse(env: L_Env, tokens: L_Tokens): L_Nodes.ProveNode {
  const skipper = new Skipper(env, tokens);

  try {
    let byContradict = false;
    if (tokens.peek() === L_KW.ProveByContradiction) {
      byContradict = true;
      skipper.skip(L_KW.ProveByContradiction);
    } else {
      skipper.skip(L_KW.Prove);
    }

    const toProve = factParse(env, tokens);

    const block: L_Node[] = [];
    skipper.skip("{");
    while (tokens.peek() !== "}") {
      while (isCurToken(tokens, L_KW.L_End)) {
        skipper.skip();
      }
      if (tokens.peek() === "}") break;

      const node = parseSingleNode(env, tokens);
      if (node !== null) block.push(node);
      else {
        throw Error();
      }
    }

    skipper.skip("}");

    if (byContradict) {
      // const contradict = optToCheckParse(env, tokens, [], true);
      const contradict = optFactParseVarsDeclared(env, tokens);
      skipper.skip(L_KW.L_End);
      return new L_Nodes.ProveContradictNode(toProve, block, contradict);
    } else {
      return new L_Nodes.ProveNode(toProve, block);
    }
  } catch (error) {
    messageParsingError(proveParse, error);
    throw error;
  }
}

function formulaSubNodeParse(env: L_Env, tokens: L_Tokens): FormulaSubNode {
  const skipper = new Skipper(env, tokens);

  try {
    // parse boolean factual formula
    if (isCurToken(tokens, "(")) {
      // skipper.skip(  "(");
      const out = parseFactFormula(env, tokens, "(", ")");
      // skipper.skip(  ")");
      return out;
    } else {
      // return optToCheckParse(env, tokens, freeFixedPairs, true);
      return optFactParse(env, tokens);
    }
  } catch (error) {
    messageParsingError(formulaSubNodeParse, error);
    throw error;
  }
}

function factParse(env: L_Env, tokens: L_Tokens): L_FactNode {
  const skipper = new Skipper(env, tokens);

  try {
    let isT = true;
    if (isCurToken(tokens, "not")) {
      skipper.skip("not");
      isT = false;
    }

    let out: L_FactNode | undefined = undefined;

    if (isCurToken(tokens, L_KW.All)) {
      out = allFactParse(env, tokens);
    } else if (isCurToken(tokens, L_KW.LBracket)) {
      out = factsNodeParse(env, tokens);
    } else if (isCurToken(tokens, L_KW.LFactFormula)) {
      out = parseFactFormula(env, tokens, L_KW.LFactFormula, L_KW.RFactFormula);
    } else if (
      tokens.peek() === L_KW.Dollar &&
      builtinFactNames.has(tokens.peek(1))
    ) {
      out = builtinFunctionParse(env, tokens);
    } else if (tokens.peek() === L_KW.If) {
      out = ifParse(env, tokens);
      // (out as L_Nodes.IfNode).addPrefixToVars();
    } else {
      out = optFactParse(env, tokens);
    }

    if (out === undefined) throw Error();
    if (!isT) out.isT = !out.isT;

    return out;
  } catch (error) {
    messageParsingError(factParse, error);
    throw error;
  }

  function allFactParse(env: L_Env, tokens: L_Tokens): FactsNode {
    const skipper = new Skipper(env, tokens);

    try {
      skipper.skip(L_KW.All);
      const vars = arrParse<L_Symbol>(
        env,
        tokens,
        SymbolParser.symbolParse,
        L_KW.Are
      );
      skipper.skip(L_KW.Are);
      const opt = optSymbolParse(env, tokens);
      const facts = vars.map((e) => new OptFactNode(opt, [e], true, undefined));
      return new FactsNode([], facts, true);
    } catch (error) {
      throw error;
    }
  }

  function factsNodeParse(env: L_Env, tokens: L_Tokens): FactsNode {
    const skipper = new Skipper(env, tokens);

    try {
      skipper.skip(L_KW.LBracket);
      const varsArrArr: [L_Singleton, L_Symbol][][] = [];
      while (!isCurToken(tokens, L_KW.RBracket)) {
        const varsArr: [L_Singleton, L_Symbol][] = [];
        while (!isCurToken(tokens, [L_KW.L_End, L_KW.RBracket])) {
          const single = SymbolParser.singletonParse(env, tokens);

          // [key: value, key] is both ok. If there is only key, then its value is key itself.
          let symbol: L_Symbol;
          if (isCurToken(tokens, L_KW.Colon)) {
            skipper.skip(L_KW.Colon);
            symbol = SymbolParser.symbolParse(env, tokens);
          } else {
            symbol = single;
          }

          varsArr.push([single, symbol]);
          if (isCurToken(tokens, L_KW.Comma)) skipper.skip(L_KW.Comma);
        }
        varsArrArr.push(varsArr);
        if (isCurToken(tokens, L_KW.L_End)) skipper.skip(L_KW.L_End);
      }

      skipper.skip(L_KW.RBracket);
      skipper.skip(L_KW.LCurlyBrace);
      const facts = arrParse<L_FactNode>(env, tokens, factParse, [
        L_KW.RCurlyBrace,
      ]);
      skipper.skip(L_KW.RCurlyBrace);
      return new FactsNode(varsArrArr, facts, true);
    } catch (error) {
      throw error;
    }
  }
}

function builtinFunctionParse(env: L_Env, tokens: L_Tokens): L_FactNode {
  const skipper = new Skipper(env, tokens);

  try {
    switch (tokens.peek(1)) {
      case L_KW.isConcept:
        return isConceptParse(env, tokens);
      case L_KW.isForm:
        return isFormParse(env, tokens);
    }

    throw Error();
  } catch (error) {
    messageParsingError(factParse, error);
    throw error;
  }
}

function parseFactFormula(
  env: L_Env,
  tokens: L_Tokens,
  begin: string,
  end: string
): FormulaSubNode {
  const skipper = new Skipper(env, tokens);

  skipper.skip(begin);

  const precedence = new Map<string, number>();
  precedence.set(L_KW.Or, 0);
  precedence.set(L_KW.And, 1);

  let isT = true;
  if (isCurToken(tokens, "not")) {
    isT = false;
    skipper.skip("not");
  }

  let left: FormulaSubNode = formulaSubNodeParse(env, tokens);
  let curOpt = skipper.skip([L_KW.Or, L_KW.And]);
  let curPrecedence = precedence.get(curOpt) as number;

  if (isCurToken(tokens, end)) {
    skipper.skip(end);
    return left;
  }

  let right: FormulaSubNode = formulaSubNodeParse(env, tokens);

  if (isCurToken(tokens, end)) {
    if (curOpt === L_KW.Or) {
      skipper.skip(end);
      return new OrToCheckNode(left, right, isT);
    } else if (curOpt === L_KW.And) {
      skipper.skip(end);
      return new AndToCheckNode(left, right, isT);
    }
  }

  while (!isCurToken(tokens, end)) {
    let nextOpt = skipper.skip([L_KW.Or, L_KW.And]);
    let nextPrecedence = precedence.get(nextOpt) as number;
    if (curPrecedence > nextPrecedence) {
      // this is true, of course. there are only 2 opts, and andPrecedence > orPrecedence
      if (curOpt === L_KW.And) {
        left = new AndToCheckNode(left, right, true);
        const next: FormulaSubNode = formulaSubNodeParse(env, tokens);
        // this is true, of course. there are only 2 opts, and andPrecedence > orPrecedence
        if (nextOpt === L_KW.Or) {
          left = new OrToCheckNode(left, next, isT);
        }
      }
    } else if (curPrecedence < nextPrecedence) {
      const next: FormulaSubNode = formulaSubNodeParse(env, tokens);
      right = new AndToCheckNode(right, next, true);
      left = new OrToCheckNode(left, right, isT);
    } else {
      if (curOpt === L_KW.And) {
        left = new AndToCheckNode(left, right, isT);
        const next: FormulaSubNode = formulaSubNodeParse(env, tokens);
        left = new AndToCheckNode(left, next, isT);
      } else {
        left = new OrToCheckNode(left, right, isT);
        const next: FormulaSubNode = formulaSubNodeParse(env, tokens);
        left = new OrToCheckNode(left, next, isT);
      }
    }
  }

  skipper.skip(end);
  return left;
}

// Main Function of parser
function factsArrParse(
  env: L_Env,
  tokens: L_Tokens,
  end: string[]
): L_FactNode[] {
  const skipper = new Skipper(env, tokens);

  try {
    const out = arrParse<L_FactNode>(env, tokens, factParse, end);
    return out;
  } catch (error) {
    messageParsingError(factsArrParse, error);
    throw error;
  }
}

function localEnvParse(env: L_Env, tokens: L_Tokens): L_Nodes.LocalEnvNode {
  const skipper = new Skipper(env, tokens);

  try {
    const localEnv = new L_Env(env);
    skipper.skip("{");
    const nodes = parseNodes(localEnv, tokens, "}");
    skipper.skip("}");
    const out = new L_Nodes.LocalEnvNode(nodes, localEnv);
    return out;
  } catch (error) {
    messageParsingError(localEnvParse, error);
    throw error;
  }
}

// TODO: vars declared
function haveParse(env: L_Env, tokens: L_Tokens): null {
  const skipper = new Skipper(env, tokens);

  try {
    skipper.skip(L_KW.Have);
    const vars = arrParse<L_Singleton>(
      env,
      tokens,
      SymbolParser.singletonParse,
      ":"
    );
    skipper.skip(L_KW.Colon);
    // const fact = optToCheckParse(env, tokens, [], false);
    const fact = optFactParse(env, tokens);
    // fact.tryFactVarsDeclared(env);
    FactVarsDeclaredChecker.check(env, fact);

    const node = new L_Nodes.HaveNode(vars, fact);

    const out = haveExec(env, node);

    return out;

    function haveExec(env: L_Env, node: L_Nodes.HaveNode): null {
      try {
        let existSymbolNum = 0;
        for (const v of node.fact.vars) {
          if (v instanceof L_Singleton) {
            if (v.value === L_KW.ExistSymbol) existSymbolNum += 1;
          }
        }

        if (node.vars.length !== existSymbolNum) throw Error();

        const out = checkFact(env, node.fact);

        if (out !== L_Structs.L_Out.True) throw Error();

        for (const v of node.vars) {
          env.tryNewPureSingleton(v.value);
        }

        const newVars: L_Symbol[] = [];
        let existSymbolAlreadyGot = 0;
        for (const v of node.fact.vars) {
          if (v instanceof L_Singleton && v.value === L_KW.ExistSymbol) {
            newVars.push(node.vars[existSymbolAlreadyGot]);
            existSymbolAlreadyGot += 1;
          } else {
            newVars.push(v);
          }
        }

        const opt = new OptFactNode(
          node.fact.optSymbol,
          newVars,
          node.fact.isT,
          node.fact.checkVars
        );

        tryNewFact(env, opt);
        return null;
      } catch (error) {
        L_Report.L_ReportErr(env, haveExec, node);
        throw error;
      }
    }
  } catch (error) {
    messageParsingError(haveParse, error);
    throw error;
  }
}

// TODO check vars introduced in def
function defConceptParse(env: L_Env, tokens: L_Tokens): null {
  const skipper = new Skipper(env, tokens);

  try {
    skipper.skip(L_KW.DefConcept);

    let commutative = false;
    if (isCurToken(tokens, L_KW.Commutative)) {
      skipper.skip(L_KW.Commutative);
      commutative = true;
    }

    // skipper.skip(  L_Keywords.FunctionalStructuredFactOptPrefix);
    // const opt = optToCheckParse(env, tokens, [], false);
    const opt = optFactParse(env, tokens);

    let cond: L_FactNode[] = [];

    if (isCurToken(tokens, ":")) {
      const newEnv = new L_Env(env);
      opt.vars.forEach((e) =>
        newEnv.tryNewPureSingleton((e as L_Singleton).value)
      );
      skipper.skip(":");
      cond = parseFactsArrCheckVarsDeclFixIfPrefix(newEnv, tokens, [
        L_KW.L_End,
        L_KW.LCurlyBrace,
      ]);
    }

    const onlyIfs: L_FactNode[] = [];
    if (isCurToken(tokens, "{")) {
      const newEnv = new L_Env(env);
      opt.vars.forEach((e) =>
        newEnv.tryNewPureSingleton((e as L_Singleton).value)
      );
      skipper.skip("{");
      onlyIfs.push(
        ...parseFactsArrCheckVarsDeclFixIfPrefix(newEnv, tokens, ["}"])
      );
      skipper.skip("}");
    } else {
      skipper.skip(L_KW.L_End);
    }

    const out = new L_Nodes.DefConceptNode(opt, cond, onlyIfs, commutative);

    if (defConceptExec(env, out) === L_Structs.L_Out.True) return null;
    else throw Error();
  } catch (error) {
    messageParsingError(defConceptParse, error);
    throw error;
  }

  function defConceptExec(
    env: L_Env,
    node: L_Nodes.DefConceptNode
  ): L_Structs.L_Out {
    try {
      declNewFact(env, node);
      node.onlyIfs.forEach((e) => env.tryFactDeclaredOrBuiltin(e));

      return L_Structs.L_Out.True;
    } catch (error) {
      messageParsingError(defConceptExec, error);
      throw error;
    }

    function declNewFact(env: L_Env, node: L_Nodes.DefConceptNode): void {
      env.tryNewDef(node.opt.optSymbol.name, node);
      for (const onlyIf of node.onlyIfs) {
        tryNewFact(env, onlyIf);
      }
    }
  }
}

function defOperatorParse(env: L_Env, tokens: L_Tokens): null {
  const skipper = new Skipper(env, tokens);

  try {
    let out: L_Nodes.DefOperatorNode | undefined = undefined;

    skipper.skip(L_KW.DefOperator);
    const composite = SymbolParser.compositeParse(env, tokens);

    if (isCurToken(tokens, L_KW.L_End)) {
      skipper.skip(L_KW.L_End);
      out = new L_Nodes.DefOperatorNode(composite, []);
    } else {
      skipper.skip(":");
      const facts: L_FactNode[] = parseFactsArrCheckVarsDeclFixIfPrefix(
        env,
        tokens,
        [L_KW.L_End],
        composite.values as L_Singleton[]
      );
      skipper.skip(L_KW.L_End);

      out = new L_Nodes.DefOperatorNode(composite, facts);
    }

    return defCompositeExec(env, out);
  } catch (error) {
    messageParsingError(defOperatorParse, error);
    throw error;
  }

  function defCompositeExec(env: L_Env, node: L_Nodes.DefOperatorNode): null {
    try {
      env.tryNewComposite(node.composite.name, node);
      env.report(`[${L_KW.DefOperator}] ${node}`);
      return null;
    } catch (error) {
      L_Report.L_ReportErr(env, defCompositeExec, node);
      return null;
    }
  }
}

export function isConceptParse(env: L_Env, tokens: L_Tokens): IsConceptNode {
  const skipper = new Skipper(env, tokens);

  try {
    skipper.skip(L_KW.Dollar);
    skipper.skip(L_KW.isConcept);
    skipper.skip(L_KW.LBrace);
    const vars = arrParse<L_Singleton>(
      env,
      tokens,
      SymbolParser.singletonParse,
      [L_KW.L_End, L_KW.RBrace]
    );

    let facts: L_FactNode[] = [];
    if (isCurToken(tokens, L_KW.L_End)) {
      skipper.skip(L_KW.L_End);
      facts = arrParse<L_FactNode>(env, tokens, factParse, [L_KW.RBrace]);
      skipper.skip(L_KW.RBrace);
    } else if (isCurToken(tokens, L_KW.RBrace)) {
      skipper.skip(L_KW.RBrace);
    }

    return new IsConceptNode(vars, facts, true);
  } catch (error) {
    messageParsingError(isConceptParse, error);
    throw error;
  }
}

export function isFormParse(env: L_Env, tokens: L_Tokens): BuiltinCheckNode {
  const skipper = new Skipper(env, tokens);

  try {
    skipper.skip(L_KW.Dollar);
    skipper.skip(L_KW.isForm);
    skipper.skip(L_KW.LBrace);
    const candidate = SymbolParser.symbolParse(env, tokens);
    skipper.skip(L_KW.L_End);
    const baseline = SymbolParser.symbolParse(env, tokens);
    if (!(baseline instanceof L_Composite))
      throw Error(`${baseline} is supposed to be a composite symbol.`);

    let facts: L_FactNode[] = [];
    if (isCurToken(tokens, L_KW.RBrace)) {
      skipper.skip(L_KW.RBrace);
    } else {
      facts = arrParse<L_FactNode>(env, tokens, factParse, [L_KW.RBrace]);
    }

    return new IsFormNode(candidate, baseline, facts, true);
  } catch (error) {
    messageParsingError(isFormParse, error);
    throw error;
  }
}

export function letsParse(env: L_Env, tokens: L_Tokens): null {
  const skipper = new Skipper(env, tokens);

  try {
    skipper.skip(L_KW.Lets);
    const name = skipper.skip();
    const regex = new RegExp(skipString(tokens));

    let node: L_Nodes.LetsNode | undefined = undefined;

    if (isCurToken(tokens, ":")) {
      skipper.skip(":");
      const facts = parseFactsArrCheckVarsDeclFixIfPrefix(
        env,
        tokens,
        [L_KW.L_End],
        [new L_Singleton(name)]
      );
      skipper.skip(L_KW.L_End);
      node = new L_Nodes.LetsNode(name, regex, facts);
    } else {
      skipper.skip(L_KW.L_End);
      node = new L_Nodes.LetsNode(name, regex, []);
    }

    const out = letsExec(env, node);
    return null;
  } catch (error) {
    messageParsingError(letsParse, error);
    throw error;
  }

  function letsExec(env: L_Env, node: L_Nodes.LetsNode): null {
    try {
      env.tryNewLetsSymbol(node);
      for (const fact of node.facts) {
        tryNewFact(env, fact);
      }
      env.report(`<lets OK!> ${node.toString()}`);
      return null;
    } catch (error) {
      L_Report.L_ReportErr(env, letsExec, node);
      throw error;
    }
  }
}

export function includeParse(env: L_Env, tokens: L_Tokens): null {
  const skipper = new Skipper(env, tokens);

  try {
    skipper.skip(L_KW.Include);

    skipper.skip('"');
    let path: string = "";
    while (!isCurToken(tokens, '"')) {
      path += skipper.skip();
    }
    skipper.skip('"');

    skipper.skip(L_KW.L_End);
    const node = new L_Nodes.IncludeNode(path);

    const out = includeExec(env, node);

    return out;

    function includeExec(env: L_Env, node: L_Nodes.IncludeNode): null {
      try {
        env.tryNewInclude(node.path);
        env.report(`[new lib included] ${node.toString()}`);
        return null;
      } catch (error) {
        L_Report.L_ReportErr(env, includeExec, node);
        return null;
      }
    }
  } catch (error) {
    messageParsingError(includeParse, error);
    throw error;
  }
}

// TODO: vars declared
export function defLiteralOperatorParse(env: L_Env, tokens: L_Tokens): null {
  const skipper = new Skipper(env, tokens);

  try {
    skipper.skip(L_KW.DefLiteralOperator);
    const name = skipper.skip();
    skipper.skip("{");
    const path = skipString(tokens);
    skipper.skip(",");
    const func = skipString(tokens);
    skipper.skip("}");

    const vars = arrParse<L_Symbol>(env, tokens, SymbolParser.symbolParse, [
      ":",
      L_KW.L_End,
    ]);

    let node: L_Nodes.DefLiteralOptNode | undefined = undefined;
    if (isCurToken(tokens, L_KW.L_End)) {
      skipper.skip(L_KW.L_End);
      node = new L_Nodes.DefLiteralOptNode(name, vars, [], path, func);
    } else {
      skipper.skip(":");
      const facts = parseFactsArrCheckVarsDeclFixIfPrefix(
        env,
        tokens,
        [L_KW.L_End],
        vars as L_Singleton[]
      );
      skipper.skip(L_KW.L_End);
      node = new L_Nodes.DefLiteralOptNode(name, vars, facts, path, func);
    }

    const out = defLiteralOptExec(env, node);

    return out;
  } catch (error) {
    messageParsingError(defLiteralOperatorParse, error);
    throw error;
  }

  function defLiteralOptExec(
    env: L_Env,
    node: L_Nodes.DefLiteralOptNode
  ): null {
    try {
      env.tryNewLiteralOpt(node);
      env.report(`[new ${L_KW.DefLiteralOperator}] ${node}`);
      return null;
    } catch (error) {
      L_Report.L_ReportErr(env, defLiteralOptExec, node);
      return null;
    }
  }
}

// export function SymbolParser.symbolParse(env: L_Env, tokens: L_Tokens): L_Symbol {
//   const skipper = new Skipper(env, tokens);

//   try {
//     let left = singleSymbolParse(env, tokens);
//     while (env.getCompositeVar(tokens.peek())) {
//       const optName = skipper.skip();
//       const right = singleSymbolParse(env, tokens);
//       left = new L_Composite(optName, [left, right]);
//     }
//     return left;
//   } catch (error) {
//     messageParsingError(isFormParse, error);
//     throw error;
//   }

//   function singleSymbolParse(env: L_Env, tokens: L_Tokens): L_Symbol {
//     // TODO Later, there should be parser based on precedence. And there does not  need ((1 * 4) + 4) = 8, there is only $ 1 * 4 + 4 = 8 $

//     try {
//       let out: L_Symbol;
//       if (tokens.peek() === L_KW.Slash) {
//         out = compositeParse(env, tokens);
//       } else if (tokens.peek() === L_KW.Dollar) {
//         out = braceCompositeParse(env, tokens);
//       } else if (tokens.peek().startsWith(L_KW.LiteralOptPrefix)) {
//         out = literalOptParse(env, tokens);
//       } else {
//         out = SymbolParser.singletonParse(env, tokens);
//       }

//       if (isCurToken(tokens, L_KW.LBracket)) {
//         const indexes: number[] = [];
//         skipper.skip(L_KW.LBracket);
//         while (!isCurToken(tokens, L_KW.RBracket)) {
//           indexes.push(parseInt(skipper.skip()));
//           if (isCurToken(tokens, L_KW.Comma)) skipper.skip(L_KW.Comma);
//         }
//         skipper.skip(L_KW.RBracket);
//         return new IndexedSymbol(out, indexes);
//       } else {
//         return out;
//       }
//     } catch (error) {
//       messageParsingError(singleSymbolParse, error);
//       throw error;
//     }
//   }
// }

// TODO: vars declared
export function letAliasParse(env: L_Env, tokens: L_Tokens): null {
  const skipper = new Skipper(env, tokens);

  try {
    skipper.skip(L_KW.LetAlias);
    const name = SymbolParser.singletonParse(env, tokens);
    skipper.skip(L_KW.Colon);
    const toBeAliased = arrParse<L_Symbol>(
      env,
      tokens,
      SymbolParser.symbolParse,
      L_KW.L_End
    );
    skipper.skip(L_KW.L_End);

    const node = new L_Nodes.LetAliasNode(name, toBeAliased);

    const out = letAliasExec(env, node);
    // L_Report.reportL_Out(env, out, node);
    return null;

    function letAliasExec(env: L_Env, node: L_Nodes.LetAliasNode): null {
      try {
        // node.toBeAliased.every((e) => e.tryVarsDeclared(env));
        node.toBeAliased.every((e) => SymbolDeclaredChecker.check(env, e));
        // if (!ok)
        //   messageParsingError(letAliasExec, `${node.toBeAliased} undeclared.`);

        env.tryNewAlias(node.name, node.toBeAliased);

        return null;
      } catch (error) {
        messageParsingError(letAliasExec, error);
        throw error;
      }
    }
  } catch (error) {
    messageParsingError(letAliasParse, error);
    throw error;
  }
}

function optFactParse(env: L_Env, tokens: L_Tokens): OptFactNode {
  const skipper = new Skipper(env, tokens);

  try {
    let isT = true;

    //TODO CheckVars not implemented

    // * If The opt starts with $, then it's an opt written like a function
    if (isCurToken(tokens, L_KW.FunctionalOptPrefix)) {
      skipper.skip(L_KW.FunctionalOptPrefix);
      const optSymbol: L_Structs.OptSymbol = optSymbolParse(env, tokens);
      skipper.skip(L_KW.LBrace);
      const vars = arrParse<L_Symbol>(
        env,
        tokens,
        SymbolParser.symbolParse,
        ")"
      );
      skipper.skip(L_KW.RBrace);

      let checkVars = checkVarsParse();

      return new OptFactNode(optSymbol, vars, isT, checkVars);
    } else {
      const var1 = SymbolParser.symbolParse(env, tokens);

      switch (tokens.peek()) {
        case "is": {
          skipper.skip("is");
          const optName = skipper.skip();
          // skipper.skip(  L_Keywords.FunctionalStructuredFactOptPrefix);
          const optSymbol = new L_Structs.OptSymbol(optName);
          let checkVars = checkVarsParse();

          return new OptFactNode(optSymbol, [var1], isT, checkVars);
        }
        // factual formulas like: a = b
        default: {
          const optName = skipper.skip();
          const optSymbol = new L_Structs.OptSymbol(optName);
          const var2 = SymbolParser.symbolParse(env, tokens);
          let checkVars = checkVarsParse();

          return new OptFactNode(optSymbol, [var1, var2], isT, checkVars);
        }
      }
    }
  } catch (error) {
    messageParsingError(optFactParse, error);
    throw error;
  }

  function checkVarsParse(): L_Symbol[][] | undefined {
    if (isCurToken(tokens, "[")) {
      skipper.skip("[");
      const checkVars: L_Symbol[][] = [];
      checkVars.push([]);
      while (!isCurToken(tokens, "]")) {
        checkVars[checkVars.length - 1].push(
          ...arrParse<L_Symbol>(env, tokens, SymbolParser.symbolParse, [
            ";",
            "]",
          ])
        );
        if (isCurToken(tokens, ";")) {
          checkVars.push([]);
          skipper.skip(";");
        }
      }
      skipper.skip("]");
      return checkVars;
    } else {
      return undefined;
    }
  }
}

function ifParse(env: L_Env, tokens: L_Tokens): IfNode {
  const skipper = new Skipper(env, tokens);

  try {
    const out = VanillaParser.ifParse(env, tokens);
    if (!out.fixUsingIfPrefix(env, [])) throw Error();
    // out.addPrefixToVars();

    // if (!out.varsDeclared(env)) {
    //   throw Error();
    // }

    return out;
  } catch (error) {
    env.getMessages().push(...env.getMessages());
    messageParsingError(ifParse, error);
    throw error;
  }
}

// 1. fix if-fact var prefix 2. check varsDeclared
function parseFactsArrCheckVarsDeclFixIfPrefix(
  env: L_Env,
  tokens: L_Tokens,
  end: string[],
  moreVars?: L_Singleton[]
): L_FactNode[] {
  const newEnv = new L_Env(env);
  if (moreVars) {
    for (const moreVar of moreVars) {
      newEnv.tryNewPureSingleton(moreVar.value);
    }
  }

  const facts = factsArrParse(newEnv, tokens, end);

  for (const fact of facts) {
    FactVarsDeclaredChecker.check(newEnv, fact);
  }

  return facts;
}

function optFactParseVarsDeclared(env: L_Env, tokens: L_Tokens): OptFactNode {
  const fact = optFactParse(env, tokens);
  FactVarsDeclaredChecker.check(env, fact);
  return fact;
}

function conceptAliasParse(env: L_Env, tokens: L_Tokens): null {
  const skipper = new Skipper(env, tokens);

  try {
    skipper.skip(L_KW.ConceptAlias);
    const name = skipper.skip();
    const toBeAliased = skipper.skip();
    skipper.skip(L_KW.L_End);
    const node = new L_Nodes.ConceptAliasNode(name, toBeAliased);
    env.tryNewConceptAlias(node);
    return null;
  } catch (error) {
    messageParsingError(conceptAliasParse, error);
    throw error;
  }
}

class VanillaParser {
  public static ifParse(env: L_Env, tokens: L_Tokens): IfNode {
    const skipper = new Skipper(env, tokens);

    try {
      skipper.skip(L_KW.If);

      // Parse vars
      const vars: L_Singleton[] = [];
      const varsForm: IfVarsFormReqType[] = [];
      while (!isCurToken(tokens, [":"])) {
        if (!isCurToken(tokens, L_KW.LBracket)) {
          const singleton = SymbolParser.singletonParse(env, tokens);
          vars.push(singleton);
        } else {
          parseBracketVars(env, tokens, vars, varsForm);
        }
        if (isCurToken(tokens, ",")) skipper.skip(",");
      }
      skipper.skip(":");

      // Parse Req
      let req: L_FactNode[] = [];
      req = arrParse<L_FactNode>(env, tokens, factParse, ["{"]);

      // Parse OnlyIfs
      skipper.skip("{");
      const onlyIfs = arrParse<L_FactNode>(env, tokens, factParse, ["}"]);
      skipper.skip("}");

      return new IfNode(vars, req, onlyIfs, true, varsForm);
    } catch (error) {
      env.getMessages().push(...env.getMessages());
      messageParsingError(ifParse, error);
      throw error;
    }

    function parseBracketVars(
      env: L_Env,
      tokens: L_Tokens,
      vars: L_Singleton[],
      varsForm: IfVarsFormReqType[]
    ) {
      skipper.skip(L_KW.LBracket);
      while (!isCurToken(tokens, L_KW.RBracket)) {
        const singleton = SymbolParser.singletonParse(env, tokens);
        vars.push(singleton);
        skipper.skip(L_KW.LBrace);
        const freeVars = arrParse<L_Singleton>(
          env,
          tokens,
          SymbolParser.singletonParse,
          L_KW.RBrace
        );
        skipper.skip(L_KW.RBrace);
        skipper.skip(L_KW.Colon);
        const symbol = SymbolParser.symbolParse(env, tokens);
        varsForm.push({ key: singleton, freeVars: freeVars, form: symbol });
        if (isCurToken(tokens, L_KW.Comma)) skipper.skip(L_KW.Comma);
      }
      skipper.skip(L_KW.RBracket);
    }
  }
}

namespace SymbolParser {
  export function symbolParse(env: L_Env, tokens: L_Tokens): L_Symbol {
    const skipper = new Skipper(env, tokens);

    try {
      let left = singleSymbolParse(env, tokens);
      while (env.getCompositeVar(tokens.peek())) {
        const optName = skipper.skip();
        const right = singleSymbolParse(env, tokens);
        left = new L_Composite(optName, [left, right]);
      }
      return left;
    } catch (error) {
      messageParsingError(isFormParse, error);
      throw error;
    }

    function singleSymbolParse(env: L_Env, tokens: L_Tokens): L_Symbol {
      // TODO Later, there should be parser based on precedence. And there does not  need ((1 * 4) + 4) = 8, there is only $ 1 * 4 + 4 = 8 $

      try {
        let out: L_Symbol;
        if (tokens.peek() === L_KW.Slash) {
          out = compositeParse(env, tokens);
        } else if (tokens.peek() === L_KW.Dollar) {
          out = braceCompositeParse(env, tokens);
        } else if (tokens.peek().startsWith(L_KW.LiteralOptPrefix)) {
          out = literalOptParse(env, tokens);
        } else {
          out = SymbolParser.singletonParse(env, tokens);
        }

        if (isCurToken(tokens, L_KW.LBracket)) {
          const indexes: number[] = [];
          skipper.skip(L_KW.LBracket);
          while (!isCurToken(tokens, L_KW.RBracket)) {
            indexes.push(parseInt(skipper.skip()));
            if (isCurToken(tokens, L_KW.Comma)) skipper.skip(L_KW.Comma);
          }
          skipper.skip(L_KW.RBracket);
          return new IndexedSymbol(out, indexes);
        } else {
          return out;
        }
      } catch (error) {
        messageParsingError(singleSymbolParse, error);
        throw error;
      }
    }
  }

  export function singletonParse(env: L_Env, tokens: L_Tokens): L_Singleton {
    const skipper = new Skipper(env, tokens);

    try {
      const value = skipper.skip();
      return new L_Singleton(value);
    } catch (error) {
      messageParsingError(SymbolParser.singletonParse, error);
      throw error;
    }
  }

  export function compositeParse(env: L_Env, tokens: L_Tokens): L_Composite {
    const skipper = new Skipper(env, tokens);

    try {
      skipper.skip(L_KW.Slash);
      const name = skipper.skip();
      skipper.skip("{");
      const values: L_Symbol[] = [];
      while (!isCurToken(tokens, "}")) {
        values.push(SymbolParser.symbolParse(env, tokens));
        if (isCurToken(tokens, ",")) skipper.skip(",");
      }
      skipper.skip("}");
      return new L_Composite(name, values);
    } catch (error) {
      messageParsingError(compositeParse, error);
      throw error;
    }
  }

  function literalOptParse(env: L_Env, tokens: L_Tokens): L_Symbol {
    const skipper = new Skipper(env, tokens);

    try {
      const name = skipper.skip().slice(L_KW.LiteralOptPrefix.length); // the # at the beginning is abandoned
      skipper.skip("{");
      const parameters: L_Symbol[] = [];
      while (!isCurToken(tokens, "}")) {
        parameters.push(SymbolParser.symbolParse(env, tokens));
        if (isCurToken(tokens, ",")) skipper.skip(",");
      }
      skipper.skip("}");

      const defLiteralOpt = env.getLiteralOpt(name);
      if (defLiteralOpt === undefined) {
        throw Error();
      }

      const external = require(defLiteralOpt.path);
      type ExternalModule = {
        [key: string]: (...args: any[]) => any;
      };

      const typedExternal = external as ExternalModule;

      let out: L_Symbol | undefined = undefined;
      for (const prop in typedExternal) {
        if (
          typeof typedExternal[prop] === "function" &&
          prop === defLiteralOpt.name
        ) {
          out = typedExternal[prop](env, ...parameters);
          if (out instanceof L_UndefinedSymbol) {
            env.report(`Invalid call of ${defLiteralOpt.name}`);
            throw Error();
          } else {
            return out as L_Symbol;
          }
        }
      }

      env.report(`literal operator ${defLiteralOpt.name} undeclared`);
      throw Error();
    } catch (error) {
      messageParsingError(literalOptParse, error);
      throw error;
    }
  }

  // TODO Later, this should be parser based on precedence
  function braceCompositeParse(env: L_Env, tokens: L_Tokens): L_Symbol {
    const skipper = new Skipper(env, tokens);

    try {
      skipper.skip(L_KW.LBrace);
      let left = SymbolParser.symbolParse(env, tokens);
      while (!isCurToken(tokens, L_KW.Dollar)) {
        const opt = optSymbolParse(env, tokens);
        const right = SymbolParser.symbolParse(env, tokens);
        left = new L_Composite(opt.name, [left, right]);
      }
      skipper.skip(L_KW.RBrace);

      return left;
    } catch (error) {
      messageParsingError(braceCompositeParse, error);
      throw error;
    }
  }

  function usePrecedenceToParseComposite(
    env: L_Env,
    tokens: L_Tokens,
    begin: string,
    end: string
  ): L_Symbol {
    const skipper = new Skipper(env, tokens);

    try {
      skipper.skip(begin);

      const precedenceMap = new Map<string, number>();
      precedenceMap.set("+", 0);
      precedenceMap.set("-", 0);
      precedenceMap.set("*", 1);
      precedenceMap.set("/", 1);

      let left = prefixSymbolParse(env, tokens);

      while (!isCurToken(tokens, end)) {
        const opt = tokens.peek();
        const next = getSymbolUntilPrecedenceIsNotHigher(
          env,
          tokens,
          end,
          precedenceMap.get(opt) as number,
          precedenceMap
        );
        left = new L_Composite(opt, [left, next]);
      }

      skipper.skip(end);
      return left as L_Symbol;
    } catch (error) {
      messageParsingError(usePrecedenceToParseComposite, error);
      throw error;
    }

    function prefixSymbolParse(env: L_Env, tokens: L_Tokens): L_Symbol {
      try {
        // TODO maybe is broken because it does not take # into consideration
        if (tokens.peek() === L_KW.Slash) {
          return SymbolParser.compositeParse(env, tokens);
        } else {
          return SymbolParser.singletonParse(env, tokens);
        }
      } catch (error) {
        messageParsingError(prefixSymbolParse, error);
        throw error;
      }
    }

    function getSymbolUntilPrecedenceIsNotHigher(
      env: L_Env,
      tokens: L_Tokens,
      end: string,
      curPrecedence: number,
      precedenceMap: Map<string, number>
    ): L_Symbol {
      let left: L_Symbol;
      if (!isCurToken(tokens, "(")) {
        left = prefixSymbolParse(env, tokens);
      } else {
        left = usePrecedenceToParseComposite(env, tokens, "(", ")");
      }

      if (isCurToken(tokens, end)) {
        return left;
      } else {
        const opt = tokens.peek();
        if ((precedenceMap.get(opt) as number) <= curPrecedence) {
          return left;
        } else {
          const next = getSymbolUntilPrecedenceIsNotHigher(
            env,
            tokens,
            end,
            precedenceMap.get(opt) as number,
            precedenceMap
          );
          return new L_Composite(opt, [left, next]);
        }
      }
    }
  }
}
