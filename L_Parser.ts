import { L_Node, LogicNode, L_FactNode, OptFactNode } from "./L_Nodes";
import * as L_Nodes from "./L_Nodes";
import { L_Env } from "./L_Env";
import { L_Keywords } from "./L_Keywords";
import * as L_Structs from "./L_Structs";
import { L_Out } from "./L_Structs";
import { L_Singleton, L_Composite, L_Symbol } from "./L_Structs";
import { isBuiltinKeyword, L_BuiltinParsers } from "./L_Builtins";
import { L_ReportParserErr, L_ReportBoolErr, L_ReportErr } from "./L_Report";
import * as L_Report from "./L_Report";
import { newFact } from "./L_Memory";
import { checkFact } from "./L_Checker";
import * as L_Memory from "./L_Memory";
import { L_Tokens } from "./L_Lexer";

// The reason why the returned valued is L_Node[] is that when checking, there might be a list of facts.
export function parseSingleNode(env: L_Env, tokens: L_Tokens): L_Node | null {
  const skipper = new Skipper(env, tokens);
  try {
    if (tokens.isEnd()) return null;

    if (isCurToken(tokens, L_Keywords.L_End)) {
      skipper.skip(env);
      while (!tokens.isEnd() && isCurToken(tokens, L_Keywords.L_End)) {
        skipper.skip(env);
      }
      if (tokens.isEnd()) return null;
    }

    if (tokens.isEnd()) {
      return null;
    }

    switch (tokens.peek()) {
      case L_Keywords.LeftCurlyBrace:
        return localEnvParse(env, tokens);
      case L_Keywords.Prove:
      case L_Keywords.ProveByContradiction:
        return proveParse(env, tokens);
    }

    switch (tokens.peek()) {
      case L_Keywords.Know:
        if (knowParse(env, tokens) === L_Out.True) return null;
      case L_Keywords.Let:
        if (letParse(env, tokens) === L_Out.True) return null;
      case L_Keywords.DefConcept:
        if (defConceptParse(env, tokens) === L_Out.True) return null;
      case L_Keywords.Have:
        // TODO: vars declared
        if (haveParse(env, tokens) === L_Out.True) return null;
      case L_Keywords.DefOperator:
        // TODO: vars declared
        if (defOperatorParse(env, tokens) === L_Out.True) return null;
      case L_Keywords.Lets:
        // TODO: vars declared
        if (letsParse(env, tokens) === L_Out.True) return null;
      case L_Keywords.Include:
        // TODO: vars declared
        if (includeParse(env, tokens) === L_Out.True) return null;
      case L_Keywords.DefLiteralOperator:
        // TODO: vars declared
        if (defLiteralOperatorParse(env, tokens) === L_Out.True) return null;
      case L_Keywords.LetFormal:
        // TODO: vars declared
        if (letFormalParse(env, tokens) === L_Out.True) return null;
      case L_Keywords.LetAlias:
        // TODO: vars declared
        if (letAliasParse(env, tokens) === L_Out.True) return null;
    }

    const fact = factParse(env, tokens);
    skipper.skip(env, L_Keywords.L_End);
    return fact;
  } catch (error) {
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
      if (isCurToken(tokens, ",")) skipper.skip(env, ",");
    }

    return out;
  } catch (error) {
    L_ReportParserErr(env, tokens, arrParse, skipper, error);
    throw error;
  }
}

function pureSingletonAndFormalSymbolParse(
  env: L_Env,
  tokens: L_Tokens
): L_Structs.L_Singleton | L_Structs.FormalSymbol {
  const skipper = new Skipper(env, tokens);

  try {
    const value = skipper.skip(env);

    if (env.isFormalSymbolDeclared(value)) {
      return new L_Structs.FormalSymbol(value);
    } else {
      return new L_Structs.L_Singleton(value);
    }
  } catch (error) {
    L_ReportParserErr(env, tokens, pureSingletonAndFormalSymbolParse, skipper);
    throw error;
  }
}

function pureSingletonParse(env: L_Env, tokens: L_Tokens): L_Singleton {
  const skipper = new Skipper(env, tokens);

  try {
    const value = skipper.skip(env);
    return new L_Structs.L_Singleton(value);
  } catch (error) {
    L_ReportParserErr(env, tokens, pureSingletonParse, skipper);
    throw error;
  }
}

function optSymbolParse(env: L_Env, tokens: L_Tokens): L_Structs.L_OptSymbol {
  const skipper = new Skipper(env, tokens);

  try {
    const name = skipper.skip(env);
    return new L_Structs.L_OptSymbol(name);
  } catch (error) {
    L_ReportParserErr(env, tokens, optSymbolParse, skipper);
    throw error;
  }
}

function compositeParse(env: L_Env, tokens: L_Tokens): L_Structs.L_Composite {
  const skipper = new Skipper(env, tokens);

  try {
    skipper.skip(env, L_Keywords.Slash);
    const name = skipper.skip(env);
    skipper.skip(env, "{");
    const values: L_Symbol[] = [];
    while (!isCurToken(tokens, "}")) {
      values.push(symbolParse(env, tokens));
      if (isCurToken(tokens, ",")) skipper.skip(env, ",");
    }
    skipper.skip(env, "}");
    return new L_Structs.L_Composite(name, values);
  } catch (error) {
    L_ReportParserErr(env, tokens, compositeParse, skipper);
    throw error;
  }
}

function literalOptParse(env: L_Env, tokens: L_Tokens): L_Symbol {
  const skipper = new Skipper(env, tokens);

  try {
    const name = skipper.skip(env).slice(L_Keywords.MacroPrefix.length); // the # at the beginning is abandoned
    skipper.skip(env, "{");
    const parameters: L_Symbol[] = [];
    while (!isCurToken(tokens, "}")) {
      parameters.push(symbolParse(env, tokens));
      if (isCurToken(tokens, ",")) skipper.skip(env, ",");
    }
    skipper.skip(env, "}");

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
        if (out instanceof L_Structs.L_UndefinedSymbol) {
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
    L_ReportParserErr(env, tokens, literalOptParse, skipper);
    throw error;
  }
}

// TODO Later, this should be parser based on precedence
function braceCompositeParse(env: L_Env, tokens: L_Tokens): L_Symbol {
  const skipper = new Skipper(env, tokens);

  try {
    skipper.skip(env, L_Keywords.LeftBrace);
    let left = symbolParse(env, tokens);
    while (!isCurToken(tokens, L_Keywords.Dollar)) {
      const opt = optSymbolParse(env, tokens);
      const right = symbolParse(env, tokens);
      left = new L_Structs.L_Composite(opt.name, [left, right]);
    }
    skipper.skip(env, L_Keywords.RightBrace);

    return left;
  } catch (error) {
    L_ReportParserErr(env, tokens, braceCompositeParse, skipper);
    throw error;
  }
}

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

  skip(env: L_Env, s: string | string[] = ""): string {
    try {
      if (typeof s === "string") {
        if (s === "") {
          const out = this.tokens.shift();
          if (out === undefined) throw Error;
          this.curTokens.push(out);
          return out;
        } else if (s === this.tokens.peek()) {
          const out = this.tokens.shift();
          if (out === undefined) throw Error;
          this.curTokens.push(out);
          return out;
        } else {
          env.report("unexpected symbol: " + this.tokens.peek());
          throw Error();
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
        env.report("unexpected symbol: " + this.tokens.peek());
        throw Error("unexpected symbol: " + this.tokens.peek());
      }
    } catch {
      throw Error();
    }
  }
}

function skip(tokens: L_Tokens, s: string | string[] = ""): string {
  try {
    if (typeof s === "string") {
      if (s === "") {
        const out = tokens.shift();
        if (out === undefined) throw Error;
        return out;
      } else if (s === tokens.peek()) {
        const out = tokens.shift();
        if (out === undefined) throw Error;
        return out;
      } else {
        throw Error("unexpected symbol: " + tokens.peek());
      }
    } else {
      for (const value of s) {
        if (value === tokens.peek()) {
          const out = tokens.shift();
          if (out === undefined) throw Error;
          return out;
        }
      }
      throw Error("unexpected symbol: " + tokens.peek());
    }
  } catch {
    throw Error();
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
  } catch {
    throw Error();
  }
}

function isCurToken(tokens: L_Tokens, s: string | string[]) {
  if (!Array.isArray(s)) {
    return s === tokens.peek();
  } else {
    return s.includes(tokens.peek());
  }
}

// @end: when parsing local env, } is the end; when parsing source code, node is the end
export function parseNodes(
  env: L_Env,
  tokens: L_Tokens,
  end: string | null
): L_Node[] {
  try {
    const out: L_Node[] = [];

    if (end === null) {
      while (!tokens.isEnd()) {
        const node = parseSingleNode(env, tokens);
        if (node !== null) out.push(node);
      }
    } else {
      while (tokens.peek() !== end) {
        const node = parseSingleNode(env, tokens);
        if (node !== null) out.push(node);
      }
    }

    return out;
  } catch (error) {
    env.report(`Error: Syntax Error.`);
    throw error;
  }
}

function knowParse(env: L_Env, tokens: L_Tokens): L_Out {
  const skipper = new Skipper(env, tokens);

  try {
    skipper.skip(env, L_Keywords.Know);

    const names: string[] = [];

    let facts: L_FactNode[] = [];
    while (!isCurToken(tokens, L_Keywords.L_End)) {
      facts = parseFactsArrCheckVarsFixIfPrefix(env, tokens, [
        L_Keywords.L_End,
        ",",
      ]);
      if (tokens.peek() === ",") skipper.skip(env, ",");
    }
    skipper.skip(env, L_Keywords.L_End);

    const out = new L_Nodes.KnowNode(facts, names);

    return knowExec(env, out);
  } catch (error) {
    L_ReportParserErr(env, tokens, knowParse, skipper);
    throw error;
  }

  function knowExec(env: L_Env, node: L_Nodes.KnowNode): L_Out {
    try {
      // examine whether all facts are declared.
      // ! NEED TO IMPLEMENT EXAMINE ALL VARS ARE DECLARED.
      if (!node.facts.every((e) => env.factDeclaredOrBuiltin(e))) throw Error();
      // if (!L_Nodes.ToCheckNode.optsDeclared(env, node.facts)) {
      //   throw Error();
      // }

      // store new knowns
      for (const onlyIf of node.facts) {
        const ok = L_Memory.newFact(env, onlyIf);
        if (!ok) {
          L_Report.reportStoreErr(env, knowExec.name, onlyIf);
          throw new Error();
        }
      }

      // for (const [i, v] of node.names.entries()) {
      //   const ok = env.newNamedKnownToCheck(v, node.facts[i]);
      //   if (!ok) throw new Error();
      // }

      return L_Out.True;
    } catch {
      return L_Report.L_ReportErr(env, knowExec, node);
    }
  }
}

function letParse(env: L_Env, tokens: L_Tokens): L_Out {
  const skipper = new Skipper(env, tokens);

  try {
    skipper.skip(env, L_Keywords.Let);

    const vars: string[] = [];
    while (![L_Keywords.L_End, , ":"].includes(tokens.peek())) {
      vars.push(skipper.skip(env));
      if (isCurToken(tokens, ",")) skipper.skip(env, ",");
    }

    if (
      vars.some(
        (e) => Object.keys(L_Keywords).includes(e) || e.startsWith("\\")
      )
    ) {
      env.report(`Error: ${vars} contain LiTeX keywords.`);
      throw Error();
    }

    let out: L_Nodes.LetNode | undefined = undefined;

    if (isCurToken(tokens, L_Keywords.L_End)) {
      skipper.skip(env, L_Keywords.L_End);
      out = new L_Nodes.LetNode(vars, []);
    } else {
      skipper.skip(env, ":");
      const facts = parseFactsArrCheckVarsFixIfPrefix(
        env,
        tokens,
        [L_Keywords.L_End],
        vars
      );
      skipper.skip(env, L_Keywords.L_End);
      out = new L_Nodes.LetNode(vars, facts);
    }

    return letExec(env, out);
  } catch (error) {
    L_ReportParserErr(env, tokens, letParse, skipper);
    throw error;
  }

  function letExec(env: L_Env, node: L_Nodes.LetNode): L_Out {
    try {
      for (const e of node.vars) {
        const ok = env.safeNewPureSingleton(e);
        if (!ok) return L_Out.Error;
      }

      if (!node.facts.every((e) => env.factDeclaredOrBuiltin(e))) {
        throw Error();
      }

      // store new facts
      for (const onlyIf of node.facts) {
        const ok = L_Memory.newFact(env, onlyIf);
        if (!ok) {
          L_Report.reportStoreErr(env, letExec.name, onlyIf);
          throw new Error();
        }
      }

      env.report(`[let] ${node}`);
      return L_Out.True;
    } catch {
      return L_Report.L_ReportErr(env, letExec, node);
    }
  }
}

// TODO: vars declared
function letFormalParse(env: L_Env, tokens: L_Tokens): L_Out {
  const skipper = new Skipper(env, tokens);

  try {
    skipper.skip(env, L_Keywords.LetFormal);

    const vars: string[] = [];
    while (![L_Keywords.L_End, , ":"].includes(tokens.peek())) {
      vars.push(skipper.skip(env));
      if (isCurToken(tokens, ",")) skipper.skip(env, ",");
    }

    if (
      vars.some(
        (e) => Object.keys(L_Keywords).includes(e) || e.startsWith("\\")
      )
    ) {
      env.report(`Error: ${vars} contain LiTeX keywords.`);
      throw Error();
    }

    let out: undefined | L_Nodes.LetFormalSymbolNode = undefined;
    if (isCurToken(tokens, L_Keywords.L_End)) {
      skipper.skip(env, L_Keywords.L_End);
      out = new L_Nodes.LetFormalSymbolNode(vars, []);
    } else {
      skipper.skip(env, ":");
      const facts = factsArrParse(env, tokens, [L_Keywords.L_End]);
      skipper.skip(env, L_Keywords.L_End);
      out = new L_Nodes.LetFormalSymbolNode(vars, facts);
    }

    if (letFormalExec(env, out) === L_Out.True) {
      return L_Out.True;
    } else {
      throw Error();
    }
  } catch (error) {
    L_ReportParserErr(env, tokens, letParse, skipper);
    throw error;
  }

  function letFormalExec(env: L_Env, node: L_Nodes.LetFormalSymbolNode): L_Out {
    try {
      for (const e of node.vars) {
        const ok = env.safeNewFormalSymbol(e);
        if (!ok) return L_Out.Error;
      }

      if (!node.facts.every((e) => env.factDeclaredOrBuiltin(e))) {
        throw Error();
      }

      for (const onlyIf of node.facts) {
        const ok = newFact(env, onlyIf);
        if (!ok) {
          L_Report.reportStoreErr(env, letFormalExec.name, onlyIf);
          throw new Error();
        }
      }

      env.report(`[let] ${node}`);
      return L_Out.True;
    } catch {
      return L_Report.L_ReportErr(env, letFormalParse, node);
    }
  }
}

function proveParse(env: L_Env, tokens: L_Tokens): L_Nodes.ProveNode {
  const skipper = new Skipper(env, tokens);

  try {
    let byContradict = false;
    if (tokens.peek() === L_Keywords.ProveByContradiction) {
      byContradict = true;
      skipper.skip(env, L_Keywords.ProveByContradiction);
    } else {
      skipper.skip(env, L_Keywords.Prove);
    }

    const toProve = factParse(env, tokens);

    const block: L_Node[] = [];
    skipper.skip(env, "{");
    while (tokens.peek() !== "}") {
      while (isCurToken(tokens, L_Keywords.L_End)) {
        skipper.skip(env);
      }
      if (tokens.peek() === "}") break;

      const node = parseSingleNode(env, tokens);
      if (node !== null) block.push(node);
      else {
        throw Error();
      }
    }

    skipper.skip(env, "}");

    if (byContradict) {
      // const contradict = optToCheckParse(env, tokens, [], true);
      const contradict = optFactParseVarsDeclared(env, tokens);
      skipper.skip(env, L_Keywords.L_End);
      return new L_Nodes.ProveContradictNode(toProve, block, contradict);
    } else {
      return new L_Nodes.ProveNode(toProve, block);
    }
  } catch (error) {
    L_ReportParserErr(env, tokens, proveParse, skipper);
    throw error;
  }
}

function formulaSubNodeParse(
  env: L_Env,
  tokens: L_Tokens
  // freeFixedPairs: [L_Symbol, L_Symbol][]
): L_Nodes.FormulaSubNode {
  const skipper = new Skipper(env, tokens);

  try {
    // parse boolean factual formula
    if (isCurToken(tokens, "(")) {
      // skipper.skip(env,  "(");
      const out = parseToCheckFormula(env, tokens, "(", ")");
      // skipper.skip(env,  ")");
      return out;
    } else {
      // return optToCheckParse(env, tokens, freeFixedPairs, true);
      return optFactParse(env, tokens);
    }
  } catch (error) {
    L_ReportParserErr(env, tokens, formulaSubNodeParse, skipper);
    throw error;
  }
}

function factParse(env: L_Env, tokens: L_Tokens): L_Nodes.L_FactNode {
  const skipper = new Skipper(env, tokens);

  try {
    let isT = true;
    // parse boolean factual formula
    if (isCurToken(tokens, "not")) {
      skipper.skip(env, "not");
      isT = false;
    }

    if (isCurToken(tokens, L_Keywords.LeftFactLogicalFormulaSig)) {
      const out = parseToCheckFormula(
        env,
        tokens,
        L_Keywords.LeftFactLogicalFormulaSig,
        L_Keywords.RightFactLogicalFormulaSig
      );
      out.isT = isT;
      return out;
    } else {
      let isT = true;
      if (isCurToken(tokens, "not")) {
        isT = false;
        skipper.skip(env, "not");
      }

      let out: L_Nodes.L_FactNode;

      if (isBuiltinKeyword(tokens.peek())) {
        const parser = L_BuiltinParsers.get(tokens.peek()) as Function;
        out = parser(env, tokens);
        out.isT = isT;
      } else if (["if", "iff"].includes(tokens.peek())) {
        out = ifFactParse(env, tokens);
        out.isT = isT ? out.isT : !out.isT;
      } else {
        out = optFactParse(env, tokens);
        out.isT = isT;
      }

      return out;
    }
  } catch (error) {
    L_ReportParserErr(env, tokens, factParse, skipper);
    throw error;
  }
}

function parseToCheckFormula(
  env: L_Env,
  tokens: L_Tokens,
  begin: string,
  end: string
  // freeFixedPairs: [L_Symbol, L_Symbol][]
): L_Nodes.FormulaSubNode {
  const skipper = new Skipper(env, tokens);

  skipper.skip(env, begin);

  const precedence = new Map<string, number>();
  precedence.set(L_Keywords.Or, 0);
  precedence.set(L_Keywords.And, 1);

  let isT = true;
  if (isCurToken(tokens, "not")) {
    isT = false;
    skipper.skip(env, "not");
  }

  let left: L_Nodes.FormulaSubNode = formulaSubNodeParse(env, tokens);
  let curOpt = skipper.skip(env, [L_Keywords.Or, L_Keywords.And]);
  let curPrecedence = precedence.get(curOpt) as number;

  if (isCurToken(tokens, end)) {
    skipper.skip(env, end);
    return left;
  }

  let right: L_Nodes.FormulaSubNode = formulaSubNodeParse(env, tokens);

  if (isCurToken(tokens, end)) {
    if (curOpt === L_Keywords.Or) {
      skipper.skip(env, end);
      return new L_Nodes.OrToCheckNode(left, right, isT);
    } else if (curOpt === L_Keywords.And) {
      skipper.skip(env, end);
      return new L_Nodes.AndToCheckNode(left, right, isT);
    }
  }

  while (!isCurToken(tokens, end)) {
    let nextOpt = skipper.skip(env, [L_Keywords.Or, L_Keywords.And]);
    let nextPrecedence = precedence.get(nextOpt) as number;
    if (curPrecedence > nextPrecedence) {
      // this is true, of course. there are only 2 opts, and andPrecedence > orPrecedence
      if (curOpt === L_Keywords.And) {
        left = new L_Nodes.AndToCheckNode(left, right, true);
        const next: L_Nodes.FormulaSubNode = formulaSubNodeParse(env, tokens);
        // this is true, of course. there are only 2 opts, and andPrecedence > orPrecedence
        if (nextOpt === L_Keywords.Or) {
          left = new L_Nodes.OrToCheckNode(left, next, isT);
        }
      }
    } else if (curPrecedence < nextPrecedence) {
      const next: L_Nodes.FormulaSubNode = formulaSubNodeParse(env, tokens);
      right = new L_Nodes.AndToCheckNode(right, next, true);
      left = new L_Nodes.OrToCheckNode(left, right, isT);
    } else {
      if (curOpt === L_Keywords.And) {
        left = new L_Nodes.AndToCheckNode(left, right, isT);
        const next: L_Nodes.FormulaSubNode = formulaSubNodeParse(env, tokens);
        left = new L_Nodes.AndToCheckNode(left, next, isT);
      } else {
        left = new L_Nodes.OrToCheckNode(left, right, isT);
        const next: L_Nodes.FormulaSubNode = formulaSubNodeParse(env, tokens);
        left = new L_Nodes.OrToCheckNode(left, next, isT);
      }
    }
  }

  skipper.skip(env, end);
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
    L_ReportParserErr(env, tokens, factsArrParse, skipper);
    throw error;
  }
}

function localEnvParse(env: L_Env, tokens: L_Tokens): L_Nodes.LocalEnvNode {
  const skipper = new Skipper(env, tokens);

  try {
    const localEnv = new L_Env(env);
    skipper.skip(env, "{");
    const nodes = parseNodes(localEnv, tokens, "}");
    skipper.skip(env, "}");
    const out = new L_Nodes.LocalEnvNode(nodes, localEnv);
    return out;
  } catch (error) {
    L_ReportParserErr(env, tokens, localEnvParse, skipper);
    throw error;
  }
}

// TODO: vars declared
function haveParse(env: L_Env, tokens: L_Tokens): L_Out {
  const skipper = new Skipper(env, tokens);

  try {
    skipper.skip(env, L_Keywords.Have);
    const vars = arrParse<L_Structs.L_Singleton>(
      env,
      tokens,
      pureSingletonParse,
      ":"
    );
    skipper.skip(env, L_Keywords.Colon);
    // const fact = optToCheckParse(env, tokens, [], false);
    const fact = optFactParse(env, tokens);
    if (!fact.varsDeclared(env)) return L_Out.Error;

    const node = new L_Nodes.HaveNode(vars, fact);

    const out = haveExec(env, node);

    return out;

    function haveExec(env: L_Env, node: L_Nodes.HaveNode): L_Out {
      try {
        let existSymbolNum = 0;
        for (const v of node.fact.vars) {
          if (v instanceof L_Singleton) {
            if (v.value === L_Keywords.ExistSymbol) existSymbolNum += 1;
          }
        }

        if (node.vars.length !== existSymbolNum) throw Error();

        const out = checkFact(env, node.fact);

        if (out !== L_Out.True) return out;

        for (const v of node.vars) {
          const ok = env.safeNewPureSingleton(v.value);
          if (!ok) throw Error();
        }

        const newVars: L_Symbol[] = [];
        let existSymbolAlreadyGot = 0;
        for (const v of node.fact.vars) {
          if (v instanceof L_Singleton && v.value === L_Keywords.ExistSymbol) {
            newVars.push(node.vars[existSymbolAlreadyGot]);
            existSymbolAlreadyGot += 1;
          } else {
            newVars.push(v);
          }
        }

        const opt = new L_Nodes.OptFactNode(
          node.fact.optSymbol,
          newVars,
          node.fact.isT,
          node.fact.checkVars
        );

        const ok = newFact(env, opt);
        if (ok) return L_Out.True;
        else throw Error();
      } catch {
        return L_Report.L_ReportErr(env, haveExec, node);
      }
    }
  } catch (error) {
    L_ReportParserErr(env, tokens, haveParse, skipper);
    throw error;
  }
}

// function specialParse(env: L_Env, tokens: L_Tokens): L_Nodes.SpecialNode {
//   const skipper = new Skipper(env, tokens);

//   try {
//     const keyword = skipper.skip(env);
//     switch (keyword) {
//       case L_Keywords.ClearKeyword:
//         skipper.skip(env, L_Keywords.L_End);
//         return new L_Nodes.SpecialNode(L_Keywords.ClearKeyword, null);
//       case L_Keywords.RunKeyword: {
//         const words: string[] = [];
//         while (!isCurToken(tokens, L_Keywords.L_End)) {
//           words.push(skipper.skip(env));
//         }
//         skipper.skip(env, L_Keywords.L_End);
//         return new L_Nodes.SpecialNode(L_Keywords.RunKeyword, words.join());
//       }
//       default:
//         throw Error();
//     }
//   } catch (error) {
//     L_ReportParserErr(env, tokens, specialParse, skipper);
//     throw error;
//   }
// }

// TODO check vars introduced in def
function defConceptParse(env: L_Env, tokens: L_Tokens): L_Out {
  const skipper = new Skipper(env, tokens);

  try {
    skipper.skip(env, L_Keywords.DefConcept);

    let commutative = false;
    if (isCurToken(tokens, L_Keywords.Commutative)) {
      skipper.skip(env, L_Keywords.Commutative);
      commutative = true;
    }

    // skipper.skip(env,  L_Keywords.FunctionalStructuredFactOptPrefix);
    // const opt = optToCheckParse(env, tokens, [], false);
    const opt = optFactParse(env, tokens);

    let cond: L_FactNode[] = [];

    if (isCurToken(tokens, ":")) {
      const newEnv = new L_Env(env);
      opt.vars.forEach((e) =>
        newEnv.safeNewPureSingleton((e as L_Singleton).value)
      );
      skipper.skip(env, ":");
      cond = parseFactsArrCheckVarsFixIfPrefix(newEnv, tokens, [
        L_Keywords.L_End,
        L_Keywords.LeftCurlyBrace,
      ]);
    }

    const onlyIfs: L_FactNode[] = [];
    if (isCurToken(tokens, "{")) {
      const newEnv = new L_Env(env);
      opt.vars.forEach((e) =>
        newEnv.safeNewPureSingleton((e as L_Singleton).value)
      );
      skipper.skip(env, "{");
      onlyIfs.push(...parseFactsArrCheckVarsFixIfPrefix(newEnv, tokens, ["}"]));
      skipper.skip(env, "}");
    } else {
      skipper.skip(env, L_Keywords.L_End);
    }

    const out = new L_Nodes.DefConceptNode(opt, cond, onlyIfs, commutative);

    if (defConceptExec(env, out) === L_Structs.L_Out.True) return L_Out.True;
    else throw Error();
  } catch (error) {
    L_ReportParserErr(env, tokens, defConceptParse, skipper);
    throw error;
  }

  // function getOpt(): OptNode {
  //   skipper.skip(env, L_Keywords.FunctionalStructuredFactOptPrefix);
  //   const optName = new L_Structs.L_OptSymbol(skipper.skip(env, ));
  //   skipper.skip(env, L_Keywords.LeftBrace);
  //   const vars = arrParse<L_Symbol>(
  //     env,
  //     tokens,
  //     symbolParse,
  //     undefined,
  //     L_Keywords.RightBrace,
  //     false
  //   );
  //   skipper.skip(env, L_Keywords.RightBrace);

  //   const opt = new OptNode(optName, vars, true, undefined);
  //   return opt;
  // }

  function defConceptExec(
    env: L_Env,
    node: L_Nodes.DefConceptNode
  ): L_Structs.L_Out {
    try {
      // declare new opt
      const ok = declNewFact(env, node);
      if (!ok) {
        env.report(`Failed to store ${node}`);
        return L_Structs.L_Out.Error;
      }

      if (!node.onlyIfs.every((e) => env.factDeclaredOrBuiltin(e))) {
        throw Error();
      }

      return L_Structs.L_Out.True;
    } catch {
      return L_ReportErr(env, defConceptExec, node);
    }

    function declNewFact(env: L_Env, node: L_Nodes.DefConceptNode): boolean {
      let ok = true;
      // if (node instanceof L_Nodes.DefExistNode) {
      //   ok = env.newDef(node.opt.optSymbol.name, node);
      //   ok = env.newExistDef(node.opt.optSymbol.name, node);
      // } else {
      ok = env.safeNewDef(node.opt.optSymbol.name, node);
      // }
      for (const onlyIf of node.onlyIfs) {
        const ok = newFact(env, onlyIf);
        if (!ok) return env.errMesReturnBoolean(`Failed to store ${onlyIf}`);
      }
      return ok;
    }
  }
}

// function defExistParse(env: L_Env, tokens: L_Tokens): L_Nodes.DefNode {
//   const start = tokens.peek();
//   const index = tokens.length;

//   try {
//     skipper.skip(env,  L_Keywords.def_exist);

//     let commutative = false;
//     if (isCurToken(tokens, L_Keywords.commutative)) {
//       skipper.skip(env,  L_Keywords.commutative);
//       commutative = true;
//     }

//     const opt: OptNode = optParse(env, tokens, false);

//     const existVars: L_Singleton[] = singletonArrParse(
//       env,
//       tokens,
//       [":", "{", L_Keywords.L_End],
//       false
//     );

//     let cond: ToCheckNode[] = [];
//     if (isCurToken(tokens, ":")) {
//       skipper.skip(env,  ":");
//       cond = factsArrParse(env, tokens, [L_Keywords.L_End], false);
//     }

//     const onlyIfs: ToCheckNode[] = [];
//     if (isCurToken(tokens, "{")) {
//       skipper.skip(env,  "{");
//       onlyIfs.push(...factsArrParse(env, tokens, ["}"], false));
//       skipper.skip(env,  "}");
//     } else {
//       skipper.skip(env,  L_Keywords.L_End);
//     }

//     return new L_Nodes.DefExistNode(opt, cond, onlyIfs, commutative, existVars);
//   } catch (error) {
//     L_ParseErr(env, tokens, defParse, skipper);
//     throw error;
//   }
// }

// --------------------------------------------------------
// TODO varsDeclared
export function defOperatorParse(env: L_Env, tokens: L_Tokens): L_Out {
  const skipper = new Skipper(env, tokens);

  try {
    let out: L_Nodes.DefOperatorNode | undefined = undefined;

    skipper.skip(env, L_Keywords.DefOperator);
    const composite = compositeParse(env, tokens);

    if (isCurToken(tokens, L_Keywords.L_End)) {
      skipper.skip(env, L_Keywords.L_End);
      out = new L_Nodes.DefOperatorNode(composite, []);
    } else {
      skipper.skip(env, ":");
      const facts: L_FactNode[] = [];

      while (!isCurToken(tokens, L_Keywords.L_End)) {
        facts.push(...factsArrParse(env, tokens, [",", L_Keywords.L_End]));
        if (isCurToken(tokens, ",")) skipper.skip(env, ",");
      }
      skipper.skip(env, L_Keywords.L_End);
      out = new L_Nodes.DefOperatorNode(composite, facts);
    }

    if (defCompositeExec(env, out) === L_Out.True) return L_Out.True;
    else throw Error();
  } catch (error) {
    L_ReportParserErr(env, tokens, defOperatorParse, skipper);
    throw error;
  }

  function defCompositeExec(env: L_Env, node: L_Nodes.DefOperatorNode): L_Out {
    try {
      if (!env.newComposite(node.composite.name, node)) throw Error();
      return env.report(`[new def_composite] ${node}`);
    } catch {
      return L_Report.L_ReportErr(env, defCompositeExec, node);
    }
  }
}

export function isPropertyParse(
  env: L_Env,
  tokens: L_Tokens
): L_Nodes.BuiltinCheckNode {
  const skipper = new Skipper(env, tokens);

  try {
    skipper.skip(env, L_Keywords.isProperty);
    skipper.skip(env, "(");
    const name = skipper.skip(env);
    skipper.skip(env, ")");

    return new L_Nodes.IsPropertyNode(name, true);
  } catch (error) {
    L_ReportParserErr(env, tokens, isPropertyParse, skipper);
    throw error;
  }
}

export function isFormParse(
  env: L_Env,
  tokens: L_Tokens
): L_Nodes.BuiltinCheckNode {
  const skipper = new Skipper(env, tokens);

  try {
    skipper.skip(env, L_Keywords.isForm);
    skipper.skip(env, "(");
    const given = symbolParse(env, tokens);
    skipper.skip(env, ",");
    const composite = compositeParse(env, tokens);

    if (isCurToken(tokens, ",")) {
      skipper.skip(env, ",");
      skipper.skip(env, "{");
      const facts: L_FactNode[] = [];
      while (!isCurToken(tokens, "}")) {
        facts.push(factParse(env, tokens));
        if (isCurToken(tokens, ",")) skipper.skip(env, ",");
      }
      skipper.skip(env, "}");
      skipper.skip(env, ")");
      return new L_Nodes.IsFormNode(given, composite, facts, true);
    } else {
      skipper.skip(env, ")");
      return new L_Nodes.IsFormNode(given, composite, [], true);
    }
  } catch (error) {
    L_ReportParserErr(env, tokens, isFormParse, skipper);
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
    skipper.skip(env, begin);

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
      left = new L_Structs.L_Composite(opt, [left, next]);
    }

    skipper.skip(env, end);
    return left as L_Symbol;
  } catch (error) {
    L_ReportParserErr(env, tokens, usePrecedenceToParseComposite, skipper);
    throw error;
  }

  function prefixSymbolParse(env: L_Env, tokens: L_Tokens): L_Symbol {
    try {
      // TODO maybe is broken because it does not take # into consideration
      if (tokens.peek() === L_Keywords.Slash) {
        return compositeParse(env, tokens);
      } else {
        return pureSingletonAndFormalSymbolParse(env, tokens);
      }
    } catch (error) {
      L_ReportParserErr(env, tokens, prefixSymbolParse, skipper);
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
        return new L_Structs.L_Composite(opt, [left, next]);
      }
    }
  }
}

// TODO: vars Declared?
export function letsParse(env: L_Env, tokens: L_Tokens): L_Out {
  const skipper = new Skipper(env, tokens);

  try {
    skipper.skip(env, L_Keywords.Lets);
    const name = skipper.skip(env);
    const regex = new RegExp(skipString(tokens));

    let node: L_Nodes.LetsNode | undefined = undefined;

    if (isCurToken(tokens, ":")) {
      skipper.skip(env, ":");
      const facts = factsArrParse(env, tokens, [L_Keywords.L_End]);
      skipper.skip(env, L_Keywords.L_End);
      node = new L_Nodes.LetsNode(name, regex, facts);
    } else {
      skipper.skip(env, L_Keywords.L_End);
      node = new L_Nodes.LetsNode(name, regex, []);
    }

    const out = letsExec(env, node);
    return L_Report.reportL_Out(env, out, node);
  } catch (error) {
    L_ReportParserErr(env, tokens, letsParse, skipper);
    throw error;
  }

  function letsExec(env: L_Env, node: L_Nodes.LetsNode): L_Out {
    try {
      env.safeNewLetsSymbol(node);
      for (const fact of node.facts) {
        newFact(env, fact);
      }
      env.report(`<lets OK!> ${node.toString()}`);
      return L_Out.True;
    } catch {
      return L_Report.L_ReportErr(env, letsExec, node);
    }
  }
}

// export function macroParse(env: L_Env, tokens: L_Tokens): L_Nodes.MacroNode {
//   const start = tokens.peek();
//   const index = tokens.length;

//   try {
//     skipper.skip(env,  L_Keywords.Macro);
//     const name = skipper.skip(env, );

//     skipper.skip(env,  '"');
//     const macroTokens: string[] = [];
//     while (!isCurToken(tokens, '"')) {
//       macroTokens.push(skipper.skip(env, ));
//     }
//     skipper.skip(env,  '"');

//     skipper.skip(env,  L_Keywords.L_End);
//     const out = new L_Nodes.MacroNode(name, macroTokens);

//     return out;
//   } catch (error) {
//     L_ParseErr(env, tokens, macroParse, skipper);
//     throw error;
//   }
// }

export function includeParse(env: L_Env, tokens: L_Tokens): L_Out {
  const skipper = new Skipper(env, tokens);

  try {
    skipper.skip(env, L_Keywords.Include);

    skipper.skip(env, '"');
    let path: string = "";
    while (!isCurToken(tokens, '"')) {
      path += skipper.skip(env);
    }
    skipper.skip(env, '"');

    skipper.skip(env, L_Keywords.L_End);
    const node = new L_Nodes.IncludeNode(path);

    const out = includeExec(env, node);

    return out;

    function includeExec(env: L_Env, node: L_Nodes.IncludeNode): L_Out {
      try {
        if (!env.newInclude(node.path)) throw Error();
        return env.report(`[new lib included] ${node.toString()}`);
      } catch {
        return L_Report.L_ReportErr(env, includeExec, node);
      }
    }
  } catch (error) {
    L_ReportParserErr(env, tokens, includeParse, skipper);
    throw error;
  }
}

// TODO: vars declared
export function defLiteralOperatorParse(env: L_Env, tokens: L_Tokens): L_Out {
  const skipper = new Skipper(env, tokens);

  try {
    skipper.skip(env, L_Keywords.DefLiteralOperator);
    const name = skipper.skip(env);
    skipper.skip(env, "{");
    const path = skipString(tokens);
    skipper.skip(env, ",");
    const func = skipString(tokens);
    skipper.skip(env, "}");

    const vars = arrParse<L_Symbol>(env, tokens, symbolParse, [
      ":",
      L_Keywords.L_End,
    ]);

    let node: L_Nodes.DefLiteralOptNode | undefined = undefined;
    if (isCurToken(tokens, L_Keywords.L_End)) {
      skipper.skip(env, L_Keywords.L_End);
      node = new L_Nodes.DefLiteralOptNode(name, vars, [], path, func);
    } else {
      skipper.skip(env, ":");
      const facts = arrParse<L_FactNode>(
        env,
        tokens,
        factParse,
        L_Keywords.L_End
      );
      skipper.skip(env, L_Keywords.L_End);
      node = new L_Nodes.DefLiteralOptNode(name, vars, facts, path, func);
    }

    const out = defLiteralOptExec(env, node);

    return out;
  } catch (error) {
    L_ReportParserErr(env, tokens, defLiteralOperatorParse, skipper);
    throw error;
  }

  function defLiteralOptExec(
    env: L_Env,
    node: L_Nodes.DefLiteralOptNode
  ): L_Out {
    try {
      if (!env.newLiteralOpt(node)) throw Error();
      return env.report(`[new ${L_Keywords.DefLiteralOperator}] ${node}`);
    } catch {
      return L_Report.L_ReportErr(env, defLiteralOptExec, node);
    }
  }
}

export function symbolParse(env: L_Env, tokens: L_Tokens): L_Symbol {
  const skipper = new Skipper(env, tokens);

  try {
    let left = singleSymbolParse(env, tokens);
    while (env.getCompositeVar(tokens.peek())) {
      const optName = skipper.skip(env);
      const right = singleSymbolParse(env, tokens);
      left = new L_Composite(optName, [left, right]);
    }
    return left;
  } catch (error) {
    L_ReportParserErr(env, tokens, isFormParse, skipper);
    throw error;
  }

  function singleSymbolParse(env: L_Env, tokens: L_Tokens): L_Symbol {
    // TODO Later, there should be parser based on precedence. And there does not  need ((1 * 4) + 4) = 8, there is only $ 1 * 4 + 4 = 8 $

    try {
      if (tokens.peek() === L_Keywords.Slash) {
        return compositeParse(env, tokens);
      } else if (tokens.peek() === L_Keywords.Dollar) {
        return braceCompositeParse(env, tokens);
      } else if (tokens.peek().startsWith(L_Keywords.LiteralOptPrefix)) {
        return literalOptParse(env, tokens);
      } else if (tokens.peek() === L_Keywords.IndexedSymbol) {
        return indexedSymbolParse(env, tokens);
      } else {
        // return singletonParse(env, tokens);
        return pureSingletonAndFormalSymbolParse(env, tokens);
      }
    } catch (error) {
      L_ReportParserErr(env, tokens, singleSymbolParse, skipper);
      throw error;
    }
  }
}

// TODO: vars declared
export function letAliasParse(env: L_Env, tokens: L_Tokens): L_Out {
  const skipper = new Skipper(env, tokens);

  try {
    skipper.skip(env, L_Keywords.LetAlias);
    const name = pureSingletonParse(env, tokens);
    const toBeAliased = arrParse<L_Symbol>(
      env,
      tokens,
      symbolParse,
      L_Keywords.L_End
    );
    skipper.skip(env, L_Keywords.L_End);

    const node = new L_Nodes.LetAliasNode(name, toBeAliased);

    const out = letAliasExec(env, node);
    return L_Report.reportL_Out(env, out, node);

    function letAliasExec(env: L_Env, node: L_Nodes.LetAliasNode): L_Out {
      let ok = node.toBeAliased.every((e) => e.varsDeclared(env));
      if (!ok)
        return L_ReportErr(
          env,
          letAliasExec,
          `${node.toBeAliased} undeclared.`
        );

      ok = env.safeNewAlias(node.name, node.toBeAliased);
      if (!ok)
        return L_ReportErr(
          env,
          letAliasExec,
          `declaration of ${node.name} failed`
        );
      else return L_Out.True;
    }
  } catch (error) {
    L_ReportParserErr(env, tokens, letAliasParse, skipper);
    throw error;
  }
}

// function defFunctionParse(env: L_Env, tokens: L_Tokens): L_Out {
//   const skipper = new Skipper(env, tokens);

//   try {
//     skipper.skip(env, L_Keywords.DefFunctional);

//     const funcName = skipper.skip(env);
//     skipper.skip(env, L_Keywords.LeftBrace);
//     const symbols = arrParse<L_Symbol>(
//       env,
//       tokens,
//       symbolParse,
//       L_Keywords.RightBrace
//     );
//     skipper.skip(env, L_Keywords.RightBrace);
//     const functional = new L_Structs.FunctionalSymbol(funcName, symbols);

//     let facts: ToCheckNode[] = [];
//     if (isCurToken(tokens, L_Keywords.Colon)) {
//       skipper.skip(env, L_Keywords.Colon);
//       facts = factsArrParse(env, tokens, [L_Keywords.L_End], true);
//     }

//     const node = new L_Nodes.DefFunctionalSymbolNode(functional, facts);
//     const ok = defFunctionExec(env, node);

//     return ok;

//     function defFunctionExec(
//       env: L_Env,
//       node: L_Nodes.DefFunctionalSymbolNode
//     ): L_Structs.L_Out {
//       const ok = env.newFunctionalSymbol(functional.name, node);

//       if (!ok) {
//         env.report(`Failed to store ${node}`);
//         return L_Structs.L_Out.Error;
//       }

//       return L_Out.True;
//     }
//   } catch (error) {
//     L_ReportParserErr(env, tokens, letAliasParse, skipper);
//     throw error;
//   }
// }

function optFactParse(env: L_Env, tokens: L_Tokens): OptFactNode {
  const skipper = new Skipper(env, tokens);

  try {
    let isT = true;

    //TODO CheckVars not implemented

    // * If The opt starts with $, then it's an opt written like a function
    if (isCurToken(tokens, L_Keywords.FunctionTypeFactOptPrefix)) {
      skipper.skip(env, L_Keywords.FunctionTypeFactOptPrefix);
      const optSymbol: L_Structs.L_OptSymbol = optSymbolParse(env, tokens);
      skip(tokens, "(");
      const vars = arrParse<L_Symbol>(env, tokens, symbolParse, ")");
      skip(tokens, L_Keywords.RightBrace);

      let checkVars = checkVarsParse();

      return new OptFactNode(optSymbol, vars, isT, checkVars);
    } else {
      const var1 = symbolParse(env, tokens);

      switch (tokens.peek()) {
        case "is": {
          skipper.skip(env, "is");
          const optName = skipper.skip(env);
          // skipper.skip(env,  L_Keywords.FunctionalStructuredFactOptPrefix);
          const optSymbol = new L_Structs.L_OptSymbol(optName);
          let checkVars = checkVarsParse();

          return new OptFactNode(optSymbol, [var1], isT, checkVars);
        }
        // factual formulas like: a = b
        default: {
          const optName = skipper.skip(env);
          const optSymbol = new L_Structs.L_OptSymbol(optName);
          const var2 = symbolParse(env, tokens);
          let checkVars = checkVarsParse();

          return new OptFactNode(optSymbol, [var1, var2], isT, checkVars);
        }
      }
    }
  } catch (error) {
    L_ReportParserErr(env, tokens, optFactParse, skipper);
    throw error;
  }

  function checkVarsParse(): L_Symbol[][] | undefined {
    if (isCurToken(tokens, "[")) {
      skipper.skip(env, "[");
      const checkVars: L_Symbol[][] = [];
      checkVars.push([]);
      while (!isCurToken(tokens, "]")) {
        checkVars[checkVars.length - 1].push(
          ...arrParse<L_Symbol>(env, tokens, symbolParse, [";", "]"])
        );
        if (isCurToken(tokens, ";")) {
          checkVars.push([]);
          skipper.skip(env, ";");
        }
      }
      skipper.skip(env, "]");
      return checkVars;
    } else {
      return undefined;
    }
  }
}

function ifFactParse(env: L_Env, tokens: L_Tokens): L_Nodes.IfNode {
  const skipper = new Skipper(env, tokens);

  try {
    skipper.skip(env, L_Keywords.If);

    // Parse vars
    const vars: L_Structs.L_Singleton[] = [];
    while (!isCurToken(tokens, [":", "{"])) {
      const singleton = pureSingletonParse(env, tokens);
      vars.push(singleton);
      if (isCurToken(tokens, ",")) skipper.skip(env, ",");
    }

    // Parse Req
    const req: L_FactNode[] = [];
    if (isCurToken(tokens, ":")) {
      skipper.skip(env, ":");
      while (!isCurToken(tokens, "{")) {
        const facts = factsArrParse(env, tokens, [",", "{"]);
        req.push(...facts);
        if (isCurToken(tokens, [","])) skipper.skip(env, [","]);
      }
    }

    // Parse OnlyIfs
    const onlyIfs: L_FactNode[] = [];
    skipper.skip(env, "{");
    while (!isCurToken(tokens, "}")) {
      // const facts = factsArrParse(env, tokens, [",", ";", "}"], false);
      const fact = factParse(env, tokens);
      onlyIfs.push(fact);
      if (isCurToken(tokens, [";", ","])) skipper.skip(env, [";", ","]);
    }
    skipper.skip(env, "}");

    // Refactor IfNode: add prefix to vars in IfNode and all inside facts
    let out = new L_Nodes.IfNode(vars, req, onlyIfs, env, true); //! By default isT = true
    if (!out.fixUsingIfPrefix(env, [])) throw Error();
    // out.addPrefixToVars();

    // if (!out.varsDeclared(env)) {
    //   throw Error();
    // }

    return out;
  } catch (error) {
    env.getMessages().push(...env.getMessages());
    L_ReportParserErr(env, tokens, ifFactParse, skipper);
    throw error;
  }
}

function indexedSymbolParse(
  env: L_Env,
  tokens: L_Tokens
): L_Structs.IndexedSymbol {
  const skipper = new Skipper(env, tokens);

  try {
    skipper.skip(env, L_Keywords.IndexedSymbol);
    skipper.skip(env, "{");
    const symbol = symbolParse(env, tokens);
    const indexes: number[] = [];
    skipper.skip(env, ",");
    while (!isCurToken(tokens, "}")) {
      indexes.push(Number(skipper.skip(env)));
      if (isCurToken(tokens, ",")) skipper.skip(env, ",");
    }
    skipper.skip(env, "}");

    return new L_Structs.IndexedSymbol(symbol, indexes);
  } catch (error) {
    L_ReportParserErr(env, tokens, indexedSymbolParse, skipper);
    throw error;
  }
}

// 1. fix if-fact var prefix 2. check varsDeclared
function parseFactsArrCheckVarsFixIfPrefix(
  env: L_Env,
  tokens: L_Tokens,
  end: string[],
  moreVars?: string[]
): L_FactNode[] {
  env = new L_Env(env);
  if (moreVars) {
    // 这里借用了一下env，然后假装开了一个新环境，以检查是否相关的var都被声明了
    for (const moreVar of moreVars) {
      env.safeNewPureSingleton(moreVar);
    }
  }

  const facts = factsArrParse(env, tokens, end);

  for (const fact of facts) {
    if (fact instanceof L_Nodes.IfNode) {
      fact.addPrefixToVars();
    }
    if (!fact.varsDeclared(env)) throw Error();
  }

  return facts;
}

function optFactParseVarsDeclared(env: L_Env, tokens: L_Tokens): OptFactNode {
  const node = optFactParse(env, tokens);
  if (!node.varsDeclared(env)) throw Error();
  else return node;
}

// function singletonFunctionalParse(
//   env: L_Env,
//   tokens: L_Tokens
// ): L_Structs.L_Singleton | L_Structs.FunctionalSymbol {
//   const skipper = new Skipper(env, tokens);

//   try {
//     if (tokens.peek(1) === L_Keywords.LeftBrace) {
//       return functionalSymbolParse(env, tokens);
//     } else {
//       return pureSingletonAndFormalSymbolParse(env, tokens);
//     }
//   } catch (error) {
//     L_ReportParserErr(env, tokens, pureSingletonAndFormalSymbolParse, skipper);
//     throw error;
//   }
// }

// function functionalSymbolParse(
//   env: L_Env,
//   tokens: L_Tokens
// ): L_Structs.FunctionalSymbol {
//   const skipper = new Skipper(env, tokens);

//   try {
//     const value = skipper.skip(env);

//     if (!env.getFunctionalSymbol(tokens.peek())) {
//       L_ReportErr(
//         env,
//         singletonFunctionalParse,
//         `${tokens.peek()} is not a declared functional symbol`
//       );
//       throw Error();
//     }

//     skipper.skip(env, L_Keywords.LeftBrace);
//     const symbols = arrParse<L_Symbol>(
//       env,
//       tokens,
//       symbolParse,
//       L_Keywords.RightBrace
//     );
//     skipper.skip(env, L_Keywords.RightBrace);

//     return new L_Structs.FunctionalSymbol(value, symbols);
//   } catch (error) {
//     L_ReportParserErr(env, tokens, pureSingletonAndFormalSymbolParse, skipper);
//     throw error;
//   }
// }
