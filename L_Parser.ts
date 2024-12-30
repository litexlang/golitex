import { L_Node, LogicNode, ToCheckNode, OptNode } from "./L_Nodes";
import * as L_Nodes from "./L_Nodes";
import { L_Env } from "./L_Env";
import { L_Keywords } from "./L_Keywords";
import * as L_Structs from "./L_Structs";
import { L_Out, L_Tokens } from "./L_Structs";
import { L_Singleton, L_Composite, L_Symbol } from "./L_Structs";
import { isBuiltinKeyword, L_BuiltinParsers } from "./L_Builtins";
import { L_ReportParserErr, L_ReportBoolErr, L_ReportErr } from "./L_Report";
import * as L_Report from "./L_Report";
import { newFact } from "./L_Memory";
import { checkFact } from "./L_Checker";

function arrParse<T>(
  env: L_Env,
  tokens: L_Structs.L_Tokens,
  parseFunc: Function,
  begin: string[] | string | undefined,
  end: string[] | string,
  skipEnd: boolean = true
): T[] {
  const skipper = new Skipper(env, tokens);

  try {
    if (begin !== undefined) skipper.skip(begin);
    const out: T[] = [];
    while (!isCurToken(tokens, end)) {
      out.push(parseFunc(env, tokens));
      if (isCurToken(tokens, ",")) skipper.skip(",");
    }
    if (skipEnd) skipper.skip(end);

    return out;
  } catch (error) {
    L_ReportParserErr(env, tokens, arrParse, skipper.curTokens);
    throw error;
  }
}

function indexedSymbolParse(
  env: L_Env,
  tokens: L_Structs.L_Tokens
): L_Structs.IndexedSymbol {
  const skipper = new Skipper(env, tokens);

  try {
    skipper.skip(L_Keywords.IndexedSymbolKeyword);
    skipper.skip("{");
    const symbol = symbolParse(env, tokens);
    const indexes: number[] = [];
    skipper.skip(",");
    while (!isCurToken(tokens, "}")) {
      indexes.push(Number(skipper.skip()));
      if (isCurToken(tokens, ",")) skipper.skip(",");
    }
    skipper.skip("}");

    return new L_Structs.IndexedSymbol(symbol, indexes);
  } catch (error) {
    L_ReportParserErr(env, tokens, indexedSymbolParse, skipper.curTokens);
    throw error;
  }
}

function singletonFunctionalParse(
  env: L_Env,
  tokens: L_Tokens
): L_Structs.L_Singleton | L_Structs.FunctionalSymbol {
  const skipper = new Skipper(env, tokens);

  try {
    if (tokens.peek(1) === L_Keywords.LeftBrace) {
      return functionalSymbolParse(env, tokens);
    } else {
      return pureSingletonAndFormalSymbolParse(env, tokens);
    }
  } catch (error) {
    L_ReportParserErr(
      env,
      tokens,
      pureSingletonAndFormalSymbolParse,
      skipper.curTokens
    );
    throw error;
  }
}

function functionalSymbolParse(
  env: L_Env,
  tokens: L_Tokens
): L_Structs.FunctionalSymbol {
  const skipper = new Skipper(env, tokens);

  try {
    const value = skipper.skip();

    if (!env.getFunctionalSymbol(tokens.peek())) {
      L_ReportErr(
        env,
        singletonFunctionalParse,
        `${tokens.peek()} is not a declared functional symbol`
      );
      throw Error();
    }

    skipper.skip(L_Keywords.LeftBrace);
    const symbols = arrParse<L_Symbol>(
      env,
      tokens,
      symbolParse,
      undefined,
      L_Keywords.RightBrace,
      true
    );

    return new L_Structs.FunctionalSymbol(value, symbols);
  } catch (error) {
    L_ReportParserErr(
      env,
      tokens,
      pureSingletonAndFormalSymbolParse,
      skipper.curTokens
    );
    throw error;
  }
}

function pureSingletonAndFormalSymbolParse(
  env: L_Env,
  tokens: L_Tokens
): L_Structs.L_Singleton | L_Structs.FormalSymbol {
  const skipper = new Skipper(env, tokens);

  try {
    const value = skipper.skip();

    if (env.isFormalSymbolDeclared(value)) {
      return new L_Structs.FormalSymbol(value);
    } else {
      return new L_Structs.L_Singleton(value);
    }
  } catch (error) {
    L_ReportParserErr(
      env,
      tokens,
      pureSingletonAndFormalSymbolParse,
      skipper.curTokens
    );
    throw error;
  }
}

function optSymbolParse(env: L_Env, tokens: L_Tokens): L_Structs.L_OptSymbol {
  const skipper = new Skipper(env, tokens);

  try {
    const name = skipper.skip();
    return new L_Structs.L_OptSymbol(name);
  } catch (error) {
    L_ReportParserErr(env, tokens, optSymbolParse, skipper.curTokens);
    throw error;
  }
}

function compositeParse(env: L_Env, tokens: L_Tokens): L_Structs.L_Composite {
  const skipper = new Skipper(env, tokens);

  try {
    skipper.skip(L_Keywords.SlashKeyword);
    const name = skipper.skip();
    skipper.skip("{");
    const values: L_Structs.L_Symbol[] = [];
    while (!isCurToken(tokens, "}")) {
      values.push(symbolParse(env, tokens));
      if (isCurToken(tokens, ",")) skipper.skip(",");
    }
    skipper.skip("}");
    return new L_Structs.L_Composite(name, values);
  } catch (error) {
    L_ReportParserErr(env, tokens, compositeParse, skipper.curTokens);
    throw error;
  }
}

function literalOptParse(env: L_Env, tokens: L_Tokens): L_Structs.L_Symbol {
  const skipper = new Skipper(env, tokens);

  try {
    const name = skipper.skip().slice(L_Keywords.MacroPrefix.length); // the # at the beginning is abandoned
    skipper.skip("{");
    const parameters: L_Structs.L_Symbol[] = [];
    while (!isCurToken(tokens, "}")) {
      parameters.push(symbolParse(env, tokens));
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

    let out: L_Structs.L_Symbol | undefined = undefined;
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
          return out as L_Structs.L_Symbol;
        }
      }
    }

    env.report(`literal operator ${defLiteralOpt.name} undeclared`);
    throw Error();
  } catch (error) {
    L_ReportParserErr(env, tokens, literalOptParse, skipper.curTokens);
    throw error;
  }
}

// TODO Later, this should be parser based on precedence
function braceCompositeParse(env: L_Env, tokens: L_Tokens): L_Structs.L_Symbol {
  const skipper = new Skipper(env, tokens);

  try {
    skipper.skip(L_Keywords.LeftBrace);
    let left = symbolParse(env, tokens);
    while (!isCurToken(tokens, L_Keywords.DollarKeyword)) {
      const opt = optSymbolParse(env, tokens);
      const right = symbolParse(env, tokens);
      left = new L_Structs.L_Composite(opt.name, [left, right]);
    }
    skipper.skip(L_Keywords.RightBrace);

    return left;
  } catch (error) {
    L_ReportParserErr(env, tokens, braceCompositeParse, skipper.curTokens);
    throw error;
  }
}

class Skipper {
  curTokens: string[] = [];
  tokens: L_Tokens;

  constructor(env: L_Env, tokens: L_Tokens) {
    this.tokens = tokens;
  }

  skip(s: string | string[] = ""): string {
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
  tokens: L_Structs.L_Tokens,
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

// const KeywordFunctionMap: {
//   // deno-lint-ignore ban-types
//   [key: string]: Function;
// } = {
//   know: knowParse,
//   let: letParse,
//   "{": localEnvParse,
//   def: defParse,
//   prove: proveParse,
//   prove_by_contradiction: proveParse,
//   have: haveParse,
//   clear: specialParse,
//   run: specialParse,
//   def_composite: defCompositeParse,
//   lets: letsParse,
//   // macro: macroParse,
//   include: includeParse,
//   def_literal_operator: defLiteralOperatorParse,
//   let_formal: letFormalParse,
//   let_alias: letAliasParse,
//   def_function: defFunctionParse,
// };

// The reason why the returned valued is L_Node[] is that when checking, there might be a list of facts.
export function parseSingleNode(env: L_Env, tokens: L_Tokens): L_Node | null {
  const skipper = new Skipper(env, tokens);
  try {
    if (tokens.isEnd()) return null;

    if (isCurToken(tokens, L_Keywords.L_End)) {
      skipper.skip();
      while (!tokens.isEnd() && isCurToken(tokens, L_Keywords.L_End)) {
        skipper.skip();
      }
      if (tokens.isEnd()) return null;
    }

    if (tokens.isEnd()) {
      return null;
    }

    switch (tokens.peek()) {
      case "know":
        return knowParse(env, tokens);
      case "{":
        return localEnvParse(env, tokens);
      case "prove":
      case "prove_by_contradiction":
        return proveParse(env, tokens);
      case "clear":
      case "run":
        return specialParse(env, tokens);
    }

    switch (tokens.peek()) {
      case "let":
        if (letParse(env, tokens) === L_Out.True) return null;
      case "def":
        if (defParse(env, tokens) === L_Out.True) return null;
      case "have":
        if (haveParse(env, tokens) === L_Out.True) return null;
      case "def_composite":
        if (defCompositeParse(env, tokens) === L_Out.True) return null;
      case "lets":
        if (letsParse(env, tokens) === L_Out.True) return null;
      case "include":
        if (includeParse(env, tokens) === L_Out.True) return null;
      case "def_literal_operator":
        if (defLiteralOperatorParse(env, tokens) === L_Out.True) return null;
      case "let_formal":
        if (letFormalParse(env, tokens) === L_Out.True) return null;
      case "let_alias":
        if (letAliasParse(env, tokens) === L_Out.True) return null;
      case "def_function":
        if (defFunctionParse(env, tokens) === L_Out.True) return null;
    }

    // const func = KeywordFunctionMap[tokens.peek()];
    // if (func) {
    //   const node = func(env, tokens);
    //   if (node === L_Out.True) return [];
    //   return [node];
    // } else {
    const fact = factParse(env, tokens, []);
    skipper.skip(L_Keywords.L_End);
    return fact;
    // const facts = factsArrParse(env, tokens, [L_Keywords.L_End], true);
    // return facts;
    // }
  } catch (error) {
    L_ReportParserErr(env, tokens, parseSingleNode, skipper.curTokens);
    throw error;
  }
}

function knowParse(env: L_Env, tokens: L_Tokens): L_Nodes.KnowNode {
  const skipper = new Skipper(env, tokens);

  try {
    skipper.skip(L_Keywords.KnowTypeKeywords);

    const names: string[] = [];

    let facts: ToCheckNode[] = [];
    // const strict = keyword === "know" ? false : true;

    // const knowNode: L_Nodes.KnowNode = new L_Nodes.KnowNode([], []);
    while (!isCurToken(tokens, L_Keywords.L_End)) {
      facts = factsArrParse(env, tokens, [L_Keywords.L_End, ","], [], false);
      // knowNode.facts = knowNode.facts.concat(outs);

      if (tokens.peek() === ",") skipper.skip(",");
    }
    skipper.skip(L_Keywords.L_End);

    return new L_Nodes.KnowNode(facts, names);
    // return knowNode;
  } catch (error) {
    L_ReportParserErr(env, tokens, knowParse, skipper.curTokens);
    throw error;
  }
}

function letParse(env: L_Env, tokens: L_Tokens): L_Out {
  const skipper = new Skipper(env, tokens);

  try {
    skipper.skip(L_Keywords.LetKeyword);

    const vars: string[] = [];
    while (![L_Keywords.L_End, , ":"].includes(tokens.peek())) {
      vars.push(skipper.skip());
      if (isCurToken(tokens, ",")) skipper.skip(",");
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
      skipper.skip(L_Keywords.L_End);
      out = new L_Nodes.LetNode(vars, []);
    } else {
      skipper.skip(":");
      const facts = factsArrParse(env, tokens, [L_Keywords.L_End], [], true);
      out = new L_Nodes.LetNode(vars, facts);
    }

    if (letExec(env, out) === L_Out.True) {
      return L_Out.True;
    } else {
      throw Error();
    }
  } catch (error) {
    L_ReportParserErr(env, tokens, letParse, skipper.curTokens);
    throw error;
  }

  function letExec(env: L_Env, node: L_Nodes.LetNode): L_Out {
    try {
      // examine whether some vars are already declared. if not, declare them.
      for (const e of node.vars) {
        const ok = env.safeNewPureSingleton(e);
        if (!ok) return L_Out.Error;
      }

      if (!node.facts.every((e) => env.factDeclaredOrBuiltin(e))) {
        throw Error();
      }

      // store new facts
      for (const onlyIf of node.facts) {
        const ok = newFact(env, onlyIf);
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

function letFormalParse(env: L_Env, tokens: L_Tokens): L_Out {
  const skipper = new Skipper(env, tokens);

  try {
    skipper.skip(L_Keywords.LetFormal);

    const vars: string[] = [];
    while (![L_Keywords.L_End, , ":"].includes(tokens.peek())) {
      vars.push(skipper.skip());
      if (isCurToken(tokens, ",")) skipper.skip(",");
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
      skipper.skip(L_Keywords.L_End);
      out = new L_Nodes.LetFormalSymbolNode(vars, []);
    } else {
      skipper.skip(":");
      const facts = factsArrParse(env, tokens, [L_Keywords.L_End], [], true);
      out = new L_Nodes.LetFormalSymbolNode(vars, facts);
    }

    if (letFormalExec(env, out) === L_Out.True) {
      return L_Out.True;
    } else {
      throw Error();
    }
  } catch (error) {
    L_ReportParserErr(env, tokens, letParse, skipper.curTokens);
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
    if (tokens.peek() === L_Keywords.ProveByContradictionKeyword) {
      byContradict = true;
      skipper.skip(L_Keywords.ProveByContradictionKeyword);
    } else {
      skipper.skip(L_Keywords.ProveKeywords);
    }

    const toProve = factParse(env, tokens, []);

    const block: L_Node[] = [];
    skipper.skip("{");
    while (tokens.peek() !== "}") {
      while (isCurToken(tokens, L_Keywords.L_End)) {
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
      const contradict = optFactParse(env, tokens, [], true);
      skipper.skip(L_Keywords.L_End);
      return new L_Nodes.ProveContradictNode(toProve, block, contradict);
    } else {
      return new L_Nodes.ProveNode(toProve, block);
    }
  } catch (error) {
    L_ReportParserErr(env, tokens, proveParse, skipper.curTokens);
    throw error;
  }
}

function formulaSubNodeParse(
  env: L_Env,
  tokens: L_Tokens,
  freeFixedPairs: [L_Symbol, L_Symbol][]
): L_Nodes.FormulaSubNode {
  const skipper = new Skipper(env, tokens);

  try {
    // parse boolean factual formula
    if (isCurToken(tokens, "(")) {
      // skipper.skip( "(");
      const out = parseToCheckFormula(env, tokens, "(", ")", freeFixedPairs);
      // skipper.skip( ")");
      return out;
    } else {
      return optFactParse(env, tokens, freeFixedPairs, true);
    }
  } catch (error) {
    L_ReportParserErr(env, tokens, formulaSubNodeParse, skipper.curTokens);
    throw error;
  }
}

function factParse(
  env: L_Env,
  tokens: L_Tokens,
  freeFixedPairs: [L_Symbol, L_Symbol][]
): L_Nodes.ToCheckNode {
  const skipper = new Skipper(env, tokens);

  try {
    let isT = true;
    // parse boolean factual formula
    if (isCurToken(tokens, "not")) {
      skipper.skip("not");
      isT = false;
    }

    if (isCurToken(tokens, L_Keywords.LeftFactLogicalFormulaSig)) {
      // skipper.skip( "(");
      const out = parseToCheckFormula(
        env,
        tokens,
        L_Keywords.LeftFactLogicalFormulaSig,
        L_Keywords.RightFactLogicalFormulaSig,
        freeFixedPairs
      );
      // skipper.skip( ")");
      out.isT = isT;
      return out;
    }
    // else if (isCurToken(tokens, L_Keywords.Dollar)) {
    //   skipper.skip( L_Keywords.Dollar);
    //   const left = symbolParse(env, tokens);
    //   const opt = new L_Structs.L_OptSymbol(skipper.skip());
    //   const right = symbolParse(env, tokens);
    //   skipper.skip( L_Keywords.Dollar);
    //   const out = new OptNode(opt, [left, right], isT);
    //   return out;
    // }
    else {
      const out = parsePrimitiveFact(env, tokens, freeFixedPairs);
      out.isT = isT;
      return out;
    }
  } catch (error) {
    L_ReportParserErr(env, tokens, factParse, skipper.curTokens);
    throw error;
  }
}

function parseToCheckFormula(
  env: L_Env,
  tokens: L_Tokens,
  begin: string,
  end: string,
  freeFixedPairs: [L_Symbol, L_Symbol][]
): L_Nodes.FormulaSubNode {
  const skipper = new Skipper(env, tokens);

  skipper.skip(begin);

  const precedence = new Map<string, number>();
  precedence.set(L_Keywords.OrKeyword, 0);
  precedence.set(L_Keywords.AndKeyword, 1);

  let isT = true;
  if (isCurToken(tokens, "not")) {
    isT = false;
    skipper.skip("not");
  }

  let left: L_Nodes.FormulaSubNode = formulaSubNodeParse(
    env,
    tokens,
    freeFixedPairs
  );
  let curOpt = skipper.skip([L_Keywords.OrKeyword, L_Keywords.AndKeyword]);
  let curPrecedence = precedence.get(curOpt) as number;

  if (isCurToken(tokens, end)) {
    skipper.skip(end);
    return left;
  }

  let right: L_Nodes.FormulaSubNode = formulaSubNodeParse(
    env,
    tokens,
    freeFixedPairs
  );

  if (isCurToken(tokens, end)) {
    if (curOpt === L_Keywords.OrKeyword) {
      skipper.skip(end);
      return new L_Nodes.OrToCheckNode(left, right, isT);
    } else if (curOpt === L_Keywords.AndKeyword) {
      skipper.skip(end);
      return new L_Nodes.AndToCheckNode(left, right, isT);
    }
  }

  while (!isCurToken(tokens, end)) {
    let nextOpt = skipper.skip([L_Keywords.OrKeyword, L_Keywords.AndKeyword]);
    let nextPrecedence = precedence.get(nextOpt) as number;
    if (curPrecedence > nextPrecedence) {
      // this is true, of course. there are only 2 opts, and andPrecedence > orPrecedence
      if (curOpt === L_Keywords.AndKeyword) {
        left = new L_Nodes.AndToCheckNode(left, right, true);
        const next: L_Nodes.FormulaSubNode = formulaSubNodeParse(
          env,
          tokens,
          freeFixedPairs
        );
        // this is true, of course. there are only 2 opts, and andPrecedence > orPrecedence
        if (nextOpt === L_Keywords.OrKeyword) {
          left = new L_Nodes.OrToCheckNode(left, next, isT);
        }
      }
    } else if (curPrecedence < nextPrecedence) {
      const next: L_Nodes.FormulaSubNode = formulaSubNodeParse(
        env,
        tokens,
        freeFixedPairs
      );
      right = new L_Nodes.AndToCheckNode(right, next, true);
      left = new L_Nodes.OrToCheckNode(left, right, isT);
    } else {
      if (curOpt === L_Keywords.AndKeyword) {
        left = new L_Nodes.AndToCheckNode(left, right, isT);
        const next: L_Nodes.FormulaSubNode = formulaSubNodeParse(
          env,
          tokens,
          freeFixedPairs
        );
        left = new L_Nodes.AndToCheckNode(left, next, isT);
      } else {
        left = new L_Nodes.OrToCheckNode(left, right, isT);
        const next: L_Nodes.FormulaSubNode = formulaSubNodeParse(
          env,
          tokens,
          freeFixedPairs
        );
        left = new L_Nodes.OrToCheckNode(left, next, isT);
      }
    }
  }

  skipper.skip(end);
  return left;
}

function parsePrimitiveFact(
  env: L_Env,
  tokens: L_Tokens,
  freeFixedPairs: [L_Symbol, L_Symbol][]
): L_Nodes.ToCheckNode {
  const skipper = new Skipper(env, tokens);

  let isT = true;
  if (isCurToken(tokens, "not")) {
    isT = false;
    skipper.skip("not");
  }

  let out: L_Nodes.ToCheckNode;

  if (isBuiltinKeyword(tokens.peek())) {
    const parser = L_BuiltinParsers.get(tokens.peek()) as Function;
    out = parser(env, tokens);
    out.isT = isT;
  } else if (["if", "iff"].includes(tokens.peek())) {
    out = ifParse(env, tokens, freeFixedPairs);
    out.isT = isT ? out.isT : !out.isT;
  } else {
    out = optFactParse(env, tokens, freeFixedPairs, true);
    out.isT = isT;
  }

  return out;
}

// Main Function of parser
function factsArrParse(
  env: L_Env,
  tokens: L_Tokens,
  end: string[],
  freeFixedPairs: [L_Symbol, L_Symbol][],
  skipEnd: boolean
): ToCheckNode[] {
  const skipper = new Skipper(env, tokens);

  try {
    let out: ToCheckNode[] = [];

    while (!end.includes(tokens.peek())) {
      const cur = factParse(env, tokens, freeFixedPairs);
      out.push(cur);
      // End of former singleNodeFacts logic

      if (isCurToken(tokens, ",")) skipper.skip(",");
    }

    if (skipEnd) skipper.skip(end);

    return out;
  } catch (error) {
    L_ReportParserErr(env, tokens, factsArrParse, skipper.curTokens);
    throw error;
  }
}

function optFactParse(
  env: L_Env,
  tokens: L_Tokens,
  freeFixPairs: [L_Symbol, L_Symbol][],
  parseNot: boolean
): OptNode {
  const skipper = new Skipper(env, tokens);

  try {
    let isT = true;

    //TODO CheckVars not implemented

    // * If The opt starts with $, then it's an opt written like a function
    if (isCurToken(tokens, L_Keywords.FunctionalStructuredFactOptPrefix)) {
      skipper.skip(L_Keywords.FunctionalStructuredFactOptPrefix);
      const optSymbol: L_Structs.L_OptSymbol = optSymbolParse(env, tokens);
      const vars = arrParse<L_Symbol>(env, tokens, symbolParse, "(", ")").map(
        (e) => e.fix(env, freeFixPairs)
      );

      let checkVars = checkVarsParse();
      if (checkVars !== undefined) {
        checkVars = checkVars.map((e) =>
          e.map((v) => v.fix(env, freeFixPairs))
        );
      }

      return new OptNode(optSymbol, vars, isT, checkVars);
    } else {
      const var1 = symbolParse(env, tokens).fix(env, freeFixPairs);

      switch (tokens.peek()) {
        case "is": {
          skipper.skip("is");
          const optName = skipper.skip();
          // skipper.skip( L_Keywords.FunctionalStructuredFactOptPrefix);
          const optSymbol = new L_Structs.L_OptSymbol(optName);
          let checkVars = checkVarsParse();
          if (checkVars !== undefined) {
            checkVars = checkVars.map((e) =>
              e.map((v) => v.fix(env, freeFixPairs))
            );
          }
          const out = new OptNode(optSymbol, [var1], isT, checkVars);
          return out;
        }
        // factual formulas like: a = b
        default: {
          const optName = skipper.skip();
          const optSymbol = new L_Structs.L_OptSymbol(optName);
          const var2 = symbolParse(env, tokens).fix(env, freeFixPairs);
          let checkVars = checkVarsParse();
          if (checkVars !== undefined) {
            checkVars = checkVars.map((e) =>
              e.map((v) => v.fix(env, freeFixPairs))
            );
          }
          const out = new OptNode(optSymbol, [var1, var2], isT, checkVars);
          return out;
        }
      }
    }
  } catch (error) {
    L_ReportParserErr(env, tokens, optFactParse, skipper.curTokens);
    throw error;
  }

  function checkVarsParse(): L_Structs.L_Symbol[][] | undefined {
    if (isCurToken(tokens, "[")) {
      skipper.skip("[");
      const checkVars: L_Structs.L_Symbol[][] = [];
      checkVars.push([]);
      while (!isCurToken(tokens, "]")) {
        checkVars[checkVars.length - 1].push(
          ...arrParse<L_Structs.L_Symbol>(
            env,
            tokens,
            symbolParse,
            undefined,
            [";", "]"],
            false
          )
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

function ifParse(
  env: L_Env,
  tokens: L_Tokens,
  freeFixedPairsFromUpper: [L_Symbol, L_Symbol][]
): L_Nodes.IfNode {
  const skipper = new Skipper(env, tokens);

  try {
    const newEnv = new L_Env(env);

    const type = skipper.skip(L_Keywords.IfKeyword);
    if (type === undefined) throw Error();
    const vars: L_Structs.L_Singleton[] = [];

    const freeFixPairs: [L_Structs.L_Symbol, L_Structs.L_Symbol][] = [
      ...freeFixedPairsFromUpper,
    ];
    while (!isCurToken(tokens, [":", "{"])) {
      const singleton = pureSingletonAndFormalSymbolParse(newEnv, tokens);

      // ! 这是必要的，因为冲突极有可能造成问题
      if (singleton instanceof L_Structs.FormalSymbol) {
        L_ReportBoolErr(
          env,
          ifParse,
          `${singleton.value} is a declared formal symbol. Free variables in logical expressions can not be formal symbol.`
        );
        throw Error();
      }

      const newSingleton = new L_Structs.L_Singleton(
        L_Keywords.IfVarPrefix + singleton.value
      );
      vars.push(newSingleton);

      newEnv.safeNewPureSingleton(newSingleton.value);

      freeFixPairs.push([singleton, newSingleton]);
      if (isCurToken(tokens, ",")) skipper.skip(",");
    }

    const reqNotFixed: ToCheckNode[] = [];
    if (isCurToken(tokens, ":")) {
      skipper.skip(":");
      while (!isCurToken(tokens, "{")) {
        const facts = factsArrParse(
          newEnv,
          tokens,
          [",", "{"],
          freeFixPairs,
          false
        );
        reqNotFixed.push(...facts);
        if (isCurToken(tokens, [","])) skipper.skip([","]);
      }
    }

    const req: ToCheckNode[] = [];
    for (const notFixed of reqNotFixed) {
      req.push(notFixed.fix(newEnv, freeFixPairs));
    }

    skipper.skip("{");

    const onlyIfs: ToCheckNode[] = [];
    while (!isCurToken(tokens, "}")) {
      // const facts = factsArrParse(env, tokens, [",", ";", "}"], false);
      const fact = factParse(newEnv, tokens, freeFixPairs);
      onlyIfs.push(fact);
      if (isCurToken(tokens, [";", ","])) skipper.skip([";", ","]);
    }
    skipper.skip("}");

    let out = new L_Nodes.IfNode(vars, req, onlyIfs, newEnv, true); //! By default isT = true

    if (out.varsDeclared(newEnv)) {
      return out;
    } else {
      env.getMessages().push(...newEnv.getMessages());
      L_Report.L_VarsInOptNotDeclaredBool(env, ifParse, out);
      throw Error();
    }
  } catch (error) {
    L_ReportParserErr(env, tokens, ifParse, skipper.curTokens);
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
    L_ReportParserErr(env, tokens, localEnvParse, skipper.curTokens);
    throw error;
  }
}

function haveParse(env: L_Env, tokens: L_Tokens): L_Out {
  const skipper = new Skipper(env, tokens);

  try {
    skipper.skip(L_Keywords.HaveKeywords);
    const vars = arrParse<L_Structs.L_Singleton>(
      env,
      tokens,
      pureSingletonAndFormalSymbolParse,
      undefined,
      ":",
      true
    );
    const fact = optFactParse(env, tokens, [], false);

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

        const opt = new L_Nodes.OptNode(
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
    L_ReportParserErr(env, tokens, haveParse, skipper.curTokens);
    throw error;
  }
}

function specialParse(env: L_Env, tokens: L_Tokens): L_Nodes.SpecialNode {
  const skipper = new Skipper(env, tokens);

  try {
    const keyword = skipper.skip();
    switch (keyword) {
      case L_Keywords.ClearKeyword:
        skipper.skip(L_Keywords.L_End);
        return new L_Nodes.SpecialNode(L_Keywords.ClearKeyword, null);
      case L_Keywords.RunKeyword: {
        const words: string[] = [];
        while (!isCurToken(tokens, L_Keywords.L_End)) {
          words.push(skipper.skip());
        }
        skipper.skip(L_Keywords.L_End);
        return new L_Nodes.SpecialNode(L_Keywords.RunKeyword, words.join());
      }
      default:
        throw Error();
    }
  } catch (error) {
    L_ReportParserErr(env, tokens, specialParse, skipper.curTokens);
    throw error;
  }
}

function defParse(env: L_Env, tokens: L_Tokens): L_Out {
  const skipper = new Skipper(env, tokens);

  try {
    skipper.skip(L_Keywords.DefFactKeywords);

    let commutative = false;
    if (isCurToken(tokens, L_Keywords.Commutative)) {
      skipper.skip(L_Keywords.Commutative);
      commutative = true;
    }

    // skipper.skip( L_Keywords.FunctionalStructuredFactOptPrefix);

    const opt: OptNode = optFactParse(env, tokens, [], false);

    let cond: ToCheckNode[] = [];
    if (isCurToken(tokens, ":")) {
      skipper.skip(":");
      cond = factsArrParse(env, tokens, [L_Keywords.L_End], [], false);
    }

    const onlyIfs: ToCheckNode[] = [];
    if (isCurToken(tokens, "{")) {
      skipper.skip("{");
      onlyIfs.push(...factsArrParse(env, tokens, ["}"], [], false));
      skipper.skip("}");
    } else {
      skipper.skip(L_Keywords.L_End);
    }

    const out = new L_Nodes.DefNode(opt, cond, onlyIfs, commutative);

    if (defExec(env, out) === L_Structs.L_Out.True) return L_Out.True;
    else throw Error();
  } catch (error) {
    L_ReportParserErr(env, tokens, defParse, skipper.curTokens);
    throw error;
  }

  function defExec(env: L_Env, node: L_Nodes.DefNode): L_Structs.L_Out {
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
      return L_ReportErr(env, defExec, node);
    }

    function declNewFact(env: L_Env, node: L_Nodes.DefNode): boolean {
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
//     skipper.skip( L_Keywords.def_exist);

//     let commutative = false;
//     if (isCurToken(tokens, L_Keywords.commutative)) {
//       skipper.skip( L_Keywords.commutative);
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
//       skipper.skip( ":");
//       cond = factsArrParse(env, tokens, [L_Keywords.L_End], false);
//     }

//     const onlyIfs: ToCheckNode[] = [];
//     if (isCurToken(tokens, "{")) {
//       skipper.skip( "{");
//       onlyIfs.push(...factsArrParse(env, tokens, ["}"], false));
//       skipper.skip( "}");
//     } else {
//       skipper.skip( L_Keywords.L_End);
//     }

//     return new L_Nodes.DefExistNode(opt, cond, onlyIfs, commutative, existVars);
//   } catch (error) {
//     L_ParseErr(env, tokens, defParse, skipper.curTokens);
//     throw error;
//   }
// }

// --------------------------------------------------------
export function defCompositeParse(env: L_Env, tokens: L_Tokens): L_Out {
  const skipper = new Skipper(env, tokens);

  try {
    let out: L_Nodes.DefCompositeNode | undefined = undefined;

    skipper.skip(L_Keywords.DefCompositeKeyword);
    const composite = compositeParse(env, tokens);

    if (isCurToken(tokens, L_Keywords.L_End)) {
      skipper.skip(L_Keywords.L_End);
      out = new L_Nodes.DefCompositeNode(composite, []);
    } else {
      skipper.skip(":");
      const facts: ToCheckNode[] = [];
      while (!isCurToken(tokens, L_Keywords.L_End)) {
        facts.push(
          ...factsArrParse(env, tokens, [",", L_Keywords.L_End], [], false)
        );
        if (isCurToken(tokens, ",")) skipper.skip(",");
      }
      skipper.skip(L_Keywords.L_End);
      out = new L_Nodes.DefCompositeNode(composite, facts);
    }

    if (defCompositeExec(env, out) === L_Out.True) return L_Out.True;
    else throw Error();
  } catch (error) {
    L_ReportParserErr(env, tokens, defCompositeParse, skipper.curTokens);
    throw error;
  }

  function defCompositeExec(env: L_Env, node: L_Nodes.DefCompositeNode): L_Out {
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
    skipper.skip(L_Keywords.isPropertyKeyword);
    skipper.skip("(");
    const name = skipper.skip();
    skipper.skip(")");

    return new L_Nodes.IsPropertyNode(name, true);
  } catch (error) {
    L_ReportParserErr(env, tokens, isPropertyParse, skipper.curTokens);
    throw error;
  }
}

export function isFormParse(
  env: L_Env,
  tokens: L_Tokens
): L_Nodes.BuiltinCheckNode {
  const skipper = new Skipper(env, tokens);

  try {
    skipper.skip(L_Keywords.isFormKeyword);
    skipper.skip("(");
    const given = symbolParse(env, tokens);
    skipper.skip(",");
    const composite = compositeParse(env, tokens);

    if (isCurToken(tokens, ",")) {
      skipper.skip(",");
      skipper.skip("{");
      const facts: ToCheckNode[] = [];
      while (!isCurToken(tokens, "}")) {
        facts.push(factParse(env, tokens, []));
        if (isCurToken(tokens, ",")) skipper.skip(",");
      }
      skipper.skip("}");
      skipper.skip(")");
      return new L_Nodes.IsFormNode(given, composite, facts, true);
    } else {
      skipper.skip(")");
      return new L_Nodes.IsFormNode(given, composite, [], true);
    }
  } catch (error) {
    L_ReportParserErr(env, tokens, isFormParse, skipper.curTokens);
    throw error;
  }
}

function usePrecedenceToParseComposite(
  env: L_Env,
  tokens: L_Tokens,
  begin: string,
  end: string
): L_Structs.L_Symbol {
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
      left = new L_Structs.L_Composite(opt, [left, next]);
    }

    skipper.skip(end);
    return left as L_Structs.L_Symbol;
  } catch (error) {
    L_ReportParserErr(
      env,
      tokens,
      usePrecedenceToParseComposite,
      skipper.curTokens
    );
    throw error;
  }

  function prefixSymbolParse(env: L_Env, tokens: L_Tokens): L_Structs.L_Symbol {
    try {
      // TODO maybe is broken because it does not take # into consideration
      if (tokens.peek() === L_Keywords.SlashKeyword) {
        return compositeParse(env, tokens);
      } else {
        return pureSingletonAndFormalSymbolParse(env, tokens);
      }
    } catch (error) {
      L_ReportParserErr(env, tokens, prefixSymbolParse, skipper.curTokens);
      throw error;
    }
  }

  function getSymbolUntilPrecedenceIsNotHigher(
    env: L_Env,
    tokens: L_Tokens,
    end: string,
    curPrecedence: number,
    precedenceMap: Map<string, number>
  ): L_Structs.L_Symbol {
    let left: L_Structs.L_Symbol;
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

export function letsParse(env: L_Env, tokens: L_Tokens): L_Out {
  const skipper = new Skipper(env, tokens);

  try {
    skipper.skip(L_Keywords.Lets);
    const name = skipper.skip();
    const regex = new RegExp(skipString(tokens));

    let node: L_Nodes.LetsNode | undefined = undefined;
    if (isCurToken(tokens, ":")) {
      skipper.skip(":");
      const facts = factsArrParse(env, tokens, [L_Keywords.L_End], [], true);
      node = new L_Nodes.LetsNode(name, regex, facts);
    } else {
      skipper.skip(L_Keywords.L_End);
      node = new L_Nodes.LetsNode(name, regex, []);
    }

    const out = letsExec(env, node);
    return L_Report.reportL_Out(env, out, node);
  } catch (error) {
    L_ReportParserErr(env, tokens, letsParse, skipper.curTokens);
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
//     skipper.skip( L_Keywords.Macro);
//     const name = skipper.skip();

//     skipper.skip( '"');
//     const macroTokens: string[] = [];
//     while (!isCurToken(tokens, '"')) {
//       macroTokens.push(skipper.skip());
//     }
//     skipper.skip( '"');

//     skipper.skip( L_Keywords.L_End);
//     const out = new L_Nodes.MacroNode(name, macroTokens);

//     return out;
//   } catch (error) {
//     L_ParseErr(env, tokens, macroParse, skipper.curTokens);
//     throw error;
//   }
// }

export function includeParse(env: L_Env, tokens: L_Tokens): L_Out {
  const skipper = new Skipper(env, tokens);

  try {
    skipper.skip(L_Keywords.Include);

    skipper.skip('"');
    let path: string = "";
    while (!isCurToken(tokens, '"')) {
      path += skipper.skip();
    }
    skipper.skip('"');

    skipper.skip(L_Keywords.L_End);
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
    L_ReportParserErr(env, tokens, includeParse, skipper.curTokens);
    throw error;
  }
}

export function defLiteralOperatorParse(env: L_Env, tokens: L_Tokens): L_Out {
  const skipper = new Skipper(env, tokens);

  try {
    skipper.skip(L_Keywords.DefLiteralOperator);
    const name = skipper.skip();
    skipper.skip("{");
    const path = skipString(tokens);
    skipper.skip(",");
    const func = skipString(tokens);
    skipper.skip("}");

    const vars = arrParse<L_Structs.L_Symbol>(
      env,
      tokens,
      symbolParse,
      undefined,
      [":", L_Keywords.L_End],
      false
    );

    let node: L_Nodes.DefLiteralOptNode | undefined = undefined;
    if (isCurToken(tokens, L_Keywords.L_End)) {
      skipper.skip(L_Keywords.L_End);
      node = new L_Nodes.DefLiteralOptNode(name, vars, [], path, func);
    } else {
      skipper.skip(":");
      const facts = arrParse<ToCheckNode>(
        env,
        tokens,
        factParse,
        undefined,
        L_Keywords.L_End,
        false
      );
      skipper.skip(L_Keywords.L_End);
      node = new L_Nodes.DefLiteralOptNode(name, vars, facts, path, func);
    }

    const out = defLiteralOptExec(env, node);

    return out;
  } catch (error) {
    L_ReportParserErr(env, tokens, defLiteralOperatorParse, skipper.curTokens);
    throw error;
  }

  function defLiteralOptExec(
    env: L_Env,
    node: L_Nodes.DefLiteralOptNode
  ): L_Out {
    try {
      if (!env.newLiteralOpt(node)) throw Error();
      return env.report(`[new def_literal_operator] ${node}`);
    } catch {
      return L_Report.L_ReportErr(env, defLiteralOptExec, node);
    }
  }
}

export function symbolParse(env: L_Env, tokens: L_Tokens): L_Structs.L_Symbol {
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
    L_ReportParserErr(env, tokens, isFormParse, skipper.curTokens);
    throw error;
  }

  function singleSymbolParse(env: L_Env, tokens: L_Tokens): L_Structs.L_Symbol {
    // TODO Later, there should be parser based on precedence. And there does not  need ((1 * 4) + 4) = 8, there is only $ 1 * 4 + 4 = 8 $

    try {
      if (tokens.peek() === L_Keywords.SlashKeyword) {
        return compositeParse(env, tokens);
      } else if (tokens.peek() === L_Keywords.DollarKeyword) {
        return braceCompositeParse(env, tokens);
      } else if (tokens.peek().startsWith(L_Keywords.LiteralOptPrefix)) {
        return literalOptParse(env, tokens);
      } else if (tokens.peek() === L_Keywords.IndexedSymbolKeyword) {
        return indexedSymbolParse(env, tokens);
      } else {
        // return singletonParse(env, tokens);
        return singletonFunctionalParse(env, tokens);
      }
    } catch (error) {
      L_ReportParserErr(env, tokens, singleSymbolParse, skipper.curTokens);
      throw error;
    }
  }
}

export function letAliasParse(env: L_Env, tokens: L_Tokens): L_Out {
  const skipper = new Skipper(env, tokens);

  try {
    skipper.skip(L_Keywords.LetAlias);
    const name = pureSingletonAndFormalSymbolParse(env, tokens);
    const toBeAliased = arrParse<L_Symbol>(
      env,
      tokens,
      symbolParse,
      undefined,
      L_Keywords.L_End,
      true
    );

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
    L_ReportParserErr(env, tokens, letAliasParse, skipper.curTokens);
    throw error;
  }
}

function defFunctionParse(env: L_Env, tokens: L_Tokens): L_Out {
  const skipper = new Skipper(env, tokens);

  try {
    skipper.skip(L_Keywords.DefFunctional);

    const funcName = skipper.skip();
    skipper.skip(L_Keywords.LeftBrace);
    const symbols = arrParse<L_Symbol>(
      env,
      tokens,
      symbolParse,
      undefined,
      L_Keywords.RightBrace,
      true
    );
    const functional = new L_Structs.FunctionalSymbol(funcName, symbols);

    let facts: ToCheckNode[] = [];
    if (isCurToken(tokens, L_Keywords.Colon)) {
      skipper.skip(L_Keywords.Colon);
      facts = factsArrParse(env, tokens, [L_Keywords.L_End], [], true);
    }

    const node = new L_Nodes.DefFunctionalSymbolNode(functional, facts);
    const ok = defFunctionExec(env, node);

    return ok;

    function defFunctionExec(
      env: L_Env,
      node: L_Nodes.DefFunctionalSymbolNode
    ): L_Structs.L_Out {
      const ok = env.newFunctionalSymbol(functional.name, node);

      if (!ok) {
        env.report(`Failed to store ${node}`);
        return L_Structs.L_Out.Error;
      }

      return L_Out.True;
    }
  } catch (error) {
    L_ReportParserErr(env, tokens, letAliasParse, skipper.curTokens);
    throw error;
  }
}
