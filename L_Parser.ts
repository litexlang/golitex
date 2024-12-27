import { L_Node, LogicNode, ToCheckNode, OptNode } from "./L_Nodes";
import * as L_Nodes from "./L_Nodes";
import { L_Env } from "./L_Env";
import { L_Keywords } from "./L_Keywords";
import * as L_Structs from "./L_Structs";
import { L_Out } from "./L_Structs";
import { L_Singleton, L_Composite, L_Symbol } from "./L_Structs";
import { isBuiltinKeyword, L_BuiltinParsers } from "./L_Builtins";
import { L_ParseErr, L_ReportBoolErr, L_ReportErr } from "./L_Report";
import * as L_Report from "./L_Report";
import { optsVarsDeclaredInFacts } from "./L_ExecutorHelper";
import { newFact } from "./L_Memory";

function arrParse<T>(
  env: L_Env,
  tokens: string[],
  parseFunc: Function,
  begin: string[] | string | undefined,
  end: string[] | string,
  skipEnd: boolean = true
): T[] {
  const start = tokens[0];
  const index = tokens.length;

  try {
    if (begin !== undefined) skip(tokens, begin);
    const out: T[] = [];
    while (!isCurToken(tokens, end)) {
      out.push(parseFunc(env, tokens));
      if (isCurToken(tokens, ",")) skip(tokens, ",");
    }
    if (skipEnd) skip(tokens, end);

    return out;
  } catch (error) {
    L_ParseErr(env, tokens, arrParse, index, start);
    throw error;
  }
}

function indexedSymbolParse(
  env: L_Env,
  tokens: string[]
): L_Structs.IndexedSymbol {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, L_Keywords.IndexedSymbolKeyword);
    skip(tokens, "{");
    const symbol = symbolParse(env, tokens);
    const indexes: number[] = [];
    skip(tokens, ",");
    while (!isCurToken(tokens, "}")) {
      indexes.push(Number(skip(tokens)));
      if (isCurToken(tokens, ",")) skip(tokens, ",");
    }
    skip(tokens, "}");

    return new L_Structs.IndexedSymbol(symbol, indexes);
  } catch (error) {
    L_ParseErr(env, tokens, indexedSymbolParse, index, start);
    throw error;
  }
}

function singletonParse(env: L_Env, tokens: string[]): L_Structs.L_Singleton {
  const start = tokens[0];
  const index = tokens.length;

  try {
    const value = skip(tokens) as string;
    return new L_Structs.L_Singleton(value);
  } catch (error) {
    L_ParseErr(env, tokens, singletonParse, index, start);
    throw error;
  }
}

function singletonArrParse(
  env: L_Env,
  tokens: string[],
  end: string | string[],
  skipEnd: boolean
): L_Structs.L_Singleton[] {
  const out: L_Structs.L_Singleton[] = [];
  while (!isCurToken(tokens, end)) {
    out.push(singletonParse(env, tokens));
    if (isCurToken(tokens, ",")) skip(tokens, ",");
  }
  if (skipEnd) skip(tokens);
  return out;
}

function optSymbolParse(env: L_Env, tokens: string[]): L_Structs.L_OptSymbol {
  const start = tokens[0];
  const index = tokens.length;

  try {
    const name = skip(tokens) as string;
    return new L_Structs.L_OptSymbol(name);
  } catch (error) {
    L_ParseErr(env, tokens, optSymbolParse, index, start);
    throw error;
  }
}

function slashCompositeParse(
  env: L_Env,
  tokens: string[]
): L_Structs.L_Composite {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, L_Keywords.SlashKeyword);
    const name = skip(tokens, tokens);
    skip(tokens, "{");
    const values: L_Structs.L_Symbol[] = [];
    while (!isCurToken(tokens, "}")) {
      values.push(symbolParse(env, tokens));
      if (isCurToken(tokens, ",")) skip(tokens, ",");
    }
    skip(tokens, "}");
    return new L_Structs.L_Composite(name, values);
  } catch (error) {
    L_ParseErr(env, tokens, slashCompositeParse, index, start);
    throw error;
  }
}

function literalOptParse(env: L_Env, tokens: string[]): L_Structs.L_Symbol {
  const start = tokens[0];
  const index = tokens.length;

  try {
    const name = skip(tokens).slice(L_Keywords.MacroPrefix.length); // the # at the beginning is abandoned
    skip(tokens, "{");
    const parameters: L_Structs.L_Symbol[] = [];
    while (!isCurToken(tokens, "}")) {
      parameters.push(symbolParse(env, tokens));
      if (isCurToken(tokens, ",")) skip(tokens, ",");
    }
    skip(tokens, "}");

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
    L_ParseErr(env, tokens, literalOptParse, index, start);
    throw error;
  }
}

// TODO Later, this should be parser based on precedence
function braceCompositeParse(env: L_Env, tokens: string[]): L_Structs.L_Symbol {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, L_Keywords.LeftBrace);
    let left = symbolParse(env, tokens);
    while (!isCurToken(tokens, L_Keywords.DollarKeyword)) {
      const opt = optSymbolParse(env, tokens);
      const right = symbolParse(env, tokens);
      left = new L_Structs.L_Composite(opt.name, [left, right]);
    }
    skip(tokens, L_Keywords.RightBrace);

    return left;
  } catch (error) {
    L_ParseErr(env, tokens, braceCompositeParse, index, start);
    throw error;
  }
}

function singleSymbolParse(env: L_Env, tokens: string[]): L_Structs.L_Symbol {
  const start = tokens[0];
  const index = tokens.length;

  // TODO Later, there should be parser based on precedence. And there does not  need ((1 * 4) + 4) = 8, there is only $ 1 * 4 + 4 = 8 $

  try {
    if (tokens[0] === L_Keywords.SlashKeyword) {
      return slashCompositeParse(env, tokens);
    } else if (tokens[0] === L_Keywords.DollarKeyword) {
      return braceCompositeParse(env, tokens);
    } else if (tokens[0].startsWith(L_Keywords.LiteralOptPrefix)) {
      return literalOptParse(env, tokens);
    } else if (tokens[0] === L_Keywords.IndexedSymbolKeyword) {
      return indexedSymbolParse(env, tokens);
    } else {
      return singletonParse(env, tokens);
    }
  } catch (error) {
    L_ParseErr(env, tokens, symbolParse, index, start);
    throw error;
  }
}

function skip(tokens: string[], s: string | string[] = ""): string {
  try {
    if (typeof s === "string") {
      if (s === "") {
        const out = tokens.shift();
        if (out === undefined) throw Error;
        return out;
      } else if (s === tokens[0]) {
        const out = tokens.shift();
        if (out === undefined) throw Error;
        return out;
      } else {
        throw Error("unexpected symbol: " + tokens[0]);
      }
    } else {
      for (const value of s) {
        if (value === tokens[0]) {
          const out = tokens.shift();
          if (out === undefined) throw Error;
          return out;
        }
      }
      throw Error("unexpected symbol: " + tokens[0]);
    }
  } catch {
    throw Error();
  }
}

// used in regex parser
function skipString(tokens: string[]): string {
  try {
    skip(tokens, '"');
    let out = "";
    while (!isCurToken(tokens, '"')) {
      out += tokens[0];
      tokens.shift();
    }
    skip(tokens, '"');
    return out;
  } catch {
    throw Error();
  }
}

function isCurToken(tokens: string[], s: string | string[]) {
  if (!Array.isArray(s)) {
    return s === tokens[0];
  } else {
    return s.includes(tokens[0]);
  }
}

// @end: when parsing local env, } is the end; when parsing source code, node is the end
export function parseNodes(
  env: L_Env,
  tokens: string[],
  end: string | null
): L_Node[] {
  try {
    const out: L_Node[] = [];

    if (end === null) {
      while (tokens.length !== 0) {
        const node = parseNodesFromSingleExpression(env, tokens);
        if (node !== undefined) out.push(...node);
      }
    } else {
      while (tokens[0] !== end) {
        const node = parseNodesFromSingleExpression(env, tokens);
        if (node !== undefined) out.push(...node);
      }
    }

    return out;
  } catch (error) {
    env.report(`Error: Syntax Error.`);
    throw error;
  }
}

const KeywordFunctionMap: {
  // deno-lint-ignore ban-types
  [key: string]: Function;
} = {
  know: knowParse,
  let: letParse,
  "{": localEnvParse,
  def: defParse,
  prove: proveParse,
  prove_by_contradiction: proveParse,
  have: haveParse,
  clear: specialParse,
  run: specialParse,
  def_composite: defCompositeParse,
  lets: letsParse,
  macro: macroParse,
  include: includeParse,
  def_literal_operator: defLiteralOperatorParse,
  // def_exist: defExistParse,
};

// The reason why the returned valued is L_Node[] is that when checking, there might be a list of facts.
export function parseNodesFromSingleExpression(
  env: L_Env,
  tokens: string[]
): L_Node[] | undefined {
  const start = tokens[0];
  const index = tokens.length;
  try {
    if (tokens.length === 0) return undefined;

    if (isCurToken(tokens, L_Keywords.L_End)) {
      tokens.shift();
      while (tokens.length > 0 && isCurToken(tokens, L_Keywords.L_End)) {
        tokens.shift();
      }
      if (tokens.length === 0) return undefined;
    }

    if (tokens.length === 0) {
      return undefined;
    }

    const func = KeywordFunctionMap[tokens[0]];
    if (func) {
      const node = func(env, tokens);
      if (node === L_Out.True) return [];
      return [node];
    } else {
      const facts = factsArrParse(env, tokens, [L_Keywords.L_End], true);
      return facts;
    }
  } catch (error) {
    L_ParseErr(env, tokens, parseNodesFromSingleExpression, index, start);
    throw error;
  }
}

function knowParse(env: L_Env, tokens: string[]): L_Nodes.KnowNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, L_Keywords.KnowTypeKeywords);

    const names: string[] = [];

    let facts: ToCheckNode[] = [];
    // const strict = keyword === "know" ? false : true;

    // const knowNode: L_Nodes.KnowNode = new L_Nodes.KnowNode([], []);
    while (!isCurToken(tokens, L_Keywords.L_End)) {
      facts = factsArrParse(env, tokens, [L_Keywords.L_End, ","], false);
      // knowNode.facts = knowNode.facts.concat(outs);

      if (tokens[0] === ",") skip(tokens, ",");
    }
    skip(tokens, L_Keywords.L_End);

    return new L_Nodes.KnowNode(facts, names);
    // return knowNode;
  } catch (error) {
    L_ParseErr(env, tokens, knowParse, index, start);
    throw error;
  }
}

function letParse(env: L_Env, tokens: string[]): L_Nodes.LetNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    const whichLet = skip(tokens, L_Keywords.LetKeyword) as string;

    const vars: string[] = [];
    while (![L_Keywords.L_End, , ":"].includes(tokens[0])) {
      vars.push(tokens.shift() as string);
      if (isCurToken(tokens, ",")) skip(tokens, ",");
    }

    if (
      vars.some(
        (e) => Object.keys(L_Keywords).includes(e) || e.startsWith("\\")
      )
    ) {
      env.report(`Error: ${vars} contain LiTeX keywords.`);
      throw Error();
    }

    if (isCurToken(tokens, L_Keywords.L_End)) {
      skip(tokens, L_Keywords.L_End);
      if (whichLet === L_Keywords.LetKeyword) {
        return new L_Nodes.LetNode(vars, []);
      } else {
        throw Error();
      }
    } else {
      skip(tokens, ":");
      const facts = factsArrParse(env, tokens, [L_Keywords.L_End], true);
      if (whichLet === L_Keywords.LetKeyword) {
        return new L_Nodes.LetNode(vars, facts);
      } else {
        throw Error();
      }
    }
  } catch (error) {
    L_ParseErr(env, tokens, letParse, index, start);
    throw error;
  }
}

function proveParse(env: L_Env, tokens: string[]): L_Nodes.ProveNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    let byContradict = false;
    if (tokens[0] === L_Keywords.ProveByContradictionKeyword) {
      byContradict = true;
      skip(tokens, L_Keywords.ProveByContradictionKeyword);
    } else {
      skip(tokens, L_Keywords.ProveKeywords);
    }

    const toProve = factParse(env, tokens);

    const block: L_Node[] = [];
    skip(tokens, "{");
    while (tokens[0] !== "}") {
      while (isCurToken(tokens, L_Keywords.L_End)) {
        tokens.shift();
      }
      if (tokens[0] === "}") break;

      const node = parseNodesFromSingleExpression(env, tokens);
      if (node !== undefined) block.push(...node);
      else {
        throw Error();
      }
    }

    skip(tokens, "}");

    if (byContradict) {
      const contradict = optParse(env, tokens, true);
      skip(tokens, L_Keywords.L_End);
      return new L_Nodes.ProveContradictNode(toProve, block, contradict);
    } else {
      return new L_Nodes.ProveNode(toProve, block);
    }
  } catch (error) {
    L_ParseErr(env, tokens, proveParse, index, start);
    throw error;
  }
}

function formulaSubNodeParse(
  env: L_Env,
  tokens: string[]
): L_Nodes.FormulaSubNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    const factStart = tokens[0];
    const factIndex = tokens.length;

    try {
      // parse boolean factual formula
      if (isCurToken(tokens, "(")) {
        // skip(tokens, "(");
        const out = parseToCheckFormula(env, tokens, "(", ")");
        // skip(tokens, ")");
        return out;
      } else {
        return optParse(env, tokens, true);
      }
    } catch (error) {
      L_ParseErr(env, tokens, formulaSubNodeParse, factIndex, factStart);
      throw error;
    }
  } catch (error) {
    L_ParseErr(env, tokens, formulaSubNodeParse, index, start);
    throw error;
  }
}

function factParse(env: L_Env, tokens: string[]): L_Nodes.ToCheckNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    const factStart = tokens[0];
    const factIndex = tokens.length;

    try {
      let isT = true;
      // parse boolean factual formula
      if (isCurToken(tokens, "not")) {
        skip(tokens, "not");
        isT = false;
      }

      if (isCurToken(tokens, L_Keywords.LeftFactLogicalFormulaSig)) {
        // skip(tokens, "(");
        const out = parseToCheckFormula(
          env,
          tokens,
          L_Keywords.LeftFactLogicalFormulaSig,
          L_Keywords.RightFactLogicalFormulaSig
        );
        // skip(tokens, ")");
        out.isT = isT;
        return out;
      }
      // else if (isCurToken(tokens, L_Keywords.Dollar)) {
      //   skip(tokens, L_Keywords.Dollar);
      //   const left = symbolParse(env, tokens);
      //   const opt = new L_Structs.L_OptSymbol(skip(tokens));
      //   const right = symbolParse(env, tokens);
      //   skip(tokens, L_Keywords.Dollar);
      //   const out = new OptNode(opt, [left, right], isT);
      //   return out;
      // }
      else {
        const out = parsePrimitiveFact(env, tokens);
        out.isT = isT;
        return out;
      }
    } catch (error) {
      L_ParseErr(env, tokens, factParse, factIndex, factStart);
      throw error;
    }
  } catch (error) {
    L_ParseErr(env, tokens, factParse, index, start);
    throw error;
  }
}

function parseToCheckFormula(
  env: L_Env,
  tokens: string[],
  begin: string,
  end: string
): L_Nodes.FormulaSubNode {
  skip(tokens, begin);

  const precedence = new Map<string, number>();
  precedence.set(L_Keywords.OrKeyword, 0);
  precedence.set(L_Keywords.AndKeyword, 1);

  let isT = true;
  if (isCurToken(tokens, "not")) {
    isT = false;
    skip(tokens, "not");
  }

  let left: L_Nodes.FormulaSubNode = formulaSubNodeParse(env, tokens);
  let curOpt = skip(tokens, [L_Keywords.OrKeyword, L_Keywords.AndKeyword]);
  let curPrecedence = precedence.get(curOpt) as number;

  if (isCurToken(tokens, end)) {
    skip(tokens, end);
    return left;
  }

  let right: L_Nodes.FormulaSubNode = formulaSubNodeParse(env, tokens);

  if (isCurToken(tokens, end)) {
    if (curOpt === L_Keywords.OrKeyword) {
      skip(tokens, end);
      return new L_Nodes.OrToCheckNode(left, right, isT);
    } else if (curOpt === L_Keywords.AndKeyword) {
      skip(tokens, end);
      return new L_Nodes.AndToCheckNode(left, right, isT);
    }
  }

  while (!isCurToken(tokens, end)) {
    let nextOpt = skip(tokens, [L_Keywords.OrKeyword, L_Keywords.AndKeyword]);
    let nextPrecedence = precedence.get(nextOpt) as number;
    if (curPrecedence > nextPrecedence) {
      // this is true, of course. there are only 2 opts, and andPrecedence > orPrecedence
      if (curOpt === L_Keywords.AndKeyword) {
        left = new L_Nodes.AndToCheckNode(left, right, true);
        const next: L_Nodes.FormulaSubNode = formulaSubNodeParse(env, tokens);
        // this is true, of course. there are only 2 opts, and andPrecedence > orPrecedence
        if (nextOpt === L_Keywords.OrKeyword) {
          left = new L_Nodes.OrToCheckNode(left, next, isT);
        }
      }
    } else if (curPrecedence < nextPrecedence) {
      const next: L_Nodes.FormulaSubNode = formulaSubNodeParse(env, tokens);
      right = new L_Nodes.AndToCheckNode(right, next, true);
      left = new L_Nodes.OrToCheckNode(left, right, isT);
    } else {
      if (curOpt === L_Keywords.AndKeyword) {
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

  skip(tokens, end);
  return left;

  throw Error();
}

function parsePrimitiveFact(env: L_Env, tokens: string[]): L_Nodes.ToCheckNode {
  let isT = true;
  if (isCurToken(tokens, "not")) {
    isT = false;
    skip(tokens, "not");
  }

  let out: L_Nodes.ToCheckNode;

  if (isBuiltinKeyword(tokens[0])) {
    const parser = L_BuiltinParsers.get(tokens[0]) as Function;
    out = parser(env, tokens);
    out.isT = isT;
  } else if (["if", "iff"].includes(tokens[0])) {
    out = logicParse(env, tokens);
    out.isT = isT ? out.isT : !out.isT;
  } else {
    out = optParse(env, tokens, true);
    out.isT = isT;
  }

  return out;
}

// Main Function of parser
function factsArrParse(
  env: L_Env,
  tokens: string[],
  end: string[],
  skipEnd: boolean
): ToCheckNode[] {
  const start = tokens[0];
  const index = tokens.length;

  try {
    let out: ToCheckNode[] = [];

    while (!end.includes(tokens[0])) {
      const cur = factParse(env, tokens);
      out.push(cur);
      // End of former singleNodeFacts logic

      if (isCurToken(tokens, ",")) skip(tokens, ",");
    }

    if (skipEnd) skip(tokens, end);

    return out;
  } catch (error) {
    L_ParseErr(env, tokens, factsArrParse, index, start);
    throw error;
  }
}

function optParse(env: L_Env, tokens: string[], parseNot: boolean): OptNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    // TODO use builtin to implement not
    let isT = true;

    // if (tokens.length >= 2 && tokens[1] === "(") {
    //   //TODO CheckVars not implemented

    //   const optSymbol: L_Structs.L_OptSymbol = optSymbolParse(env, tokens);
    //   const vars = arrParse<L_Structs.L_Symbol>(
    //     env,
    //     tokens,
    //     symbolParse,
    //     "(",
    //     ")"
    //   );

    //   let checkVars = checkVarsParse();

    //   return new OptNode(optSymbol, vars, isT, checkVars);
    // }

    // * If The opt starts with $, then it's an opt written like a function
    if (isCurToken(tokens, L_Keywords.FunctionalStructuredFactOptPrefix)) {
      skip(tokens, L_Keywords.FunctionalStructuredFactOptPrefix);
      const optSymbol: L_Structs.L_OptSymbol = optSymbolParse(env, tokens);
      const vars = arrParse<L_Symbol>(env, tokens, symbolParse, "(", ")");

      let checkVars = checkVarsParse();

      return new OptNode(optSymbol, vars, isT, checkVars);
    } else {
      const var1 = symbolParse(env, tokens);

      switch (tokens[0]) {
        case "is": {
          skip(tokens, "is");
          const optName = skip(tokens);
          // skip(tokens, L_Keywords.FunctionalStructuredFactOptPrefix);
          const optSymbol = new L_Structs.L_OptSymbol(optName);
          const checkVars = checkVarsParse();
          const out = new OptNode(optSymbol, [var1], isT, checkVars);
          return out;
        }
        default: {
          const optName = skip(tokens);
          const optSymbol = new L_Structs.L_OptSymbol(optName);
          const var2 = symbolParse(env, tokens);
          const checkVars = checkVarsParse();
          const out = new OptNode(optSymbol, [var1, var2], isT, checkVars);
          return out;
        }
      }
    }
  } catch (error) {
    L_ParseErr(env, tokens, optParse, index, start);
    throw error;
  }

  function checkVarsParse(): L_Structs.L_Symbol[][] | undefined {
    if (isCurToken(tokens, "[")) {
      skip(tokens, "[");
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
          skip(tokens, ";");
        }
      }
      skip(tokens, "]");
      return checkVars;
    } else {
      return undefined;
    }
  }
}

function logicParse(env: L_Env, tokens: string[]): LogicNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    const type = skip(tokens, [L_Keywords.IfKeyword, L_Keywords.IffKeyword]);
    if (type === undefined) throw Error();
    const vars: L_Structs.L_Singleton[] = [];

    const freeFixPairs: [L_Structs.L_Symbol, L_Structs.L_Symbol][] = [];
    while (!isCurToken(tokens, [":", "{"])) {
      const singleton = singletonParse(env, tokens);
      const newSingleton = new L_Structs.L_Singleton(
        L_Keywords.IfVarPrefix + singleton.value
      );
      vars.push(newSingleton);
      freeFixPairs.push([singleton, newSingleton]);
      if (isCurToken(tokens, ",")) skip(tokens, ",");
    }

    const req: ToCheckNode[] = [];
    if (isCurToken(tokens, ":")) {
      skip(tokens, ":");
      while (!isCurToken(tokens, "{")) {
        const facts = factsArrParse(env, tokens, [",", "{"], false);
        req.push(...facts);
        if (isCurToken(tokens, [","])) skip(tokens, [","]);
      }
    }

    skip(tokens, "{");

    const onlyIfs: ToCheckNode[] = [];
    while (!isCurToken(tokens, "}")) {
      // const facts = factsArrParse(env, tokens, [",", ";", "}"], false);
      const fact = factParse(env, tokens);
      onlyIfs.push(fact);
      if (isCurToken(tokens, [";", ","])) skip(tokens, [";", ","]);
    }
    skip(tokens, "}");

    if (type === L_Keywords.IfKeyword) {
      let out = new L_Nodes.IfNode(vars, req, onlyIfs, true); //! By default isT = true
      out = out.fix(env, freeFixPairs);
      return out;
    } else if (type === L_Keywords.IffKeyword) {
      let out = new L_Nodes.IffNode(vars, req, onlyIfs, true);
      out = out.fix(env, freeFixPairs);
      return out;
    } else {
      throw Error();
    }
  } catch (error) {
    L_ParseErr(env, tokens, logicParse, index, start);
    throw error;
  }
}

function localEnvParse(env: L_Env, tokens: string[]): L_Nodes.LocalEnvNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, "{");
    const nodes = parseNodes(env, tokens, "}");
    skip(tokens, "}");
    const out = new L_Nodes.LocalEnvNode(nodes);
    return out;
  } catch (error) {
    L_ParseErr(env, tokens, localEnvParse, index, start);
    throw error;
  }
}

function haveParse(env: L_Env, tokens: string[]): L_Nodes.HaveNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, L_Keywords.HaveKeywords);
    const vars = arrParse<L_Structs.L_Singleton>(
      env,
      tokens,
      singletonParse,
      undefined,
      ":",
      true
    );
    const fact = optParse(env, tokens, false);

    return new L_Nodes.HaveNode(vars, fact);
  } catch (error) {
    L_ParseErr(env, tokens, haveParse, index, start);
    throw error;
  }
}

function specialParse(env: L_Env, tokens: string[]): L_Nodes.SpecialNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    const keyword = tokens.shift() as string;
    switch (keyword) {
      case L_Keywords.ClearKeyword:
        skip(tokens, L_Keywords.L_End);
        return new L_Nodes.SpecialNode(L_Keywords.ClearKeyword, null);
      case L_Keywords.RunKeyword: {
        const words: string[] = [];
        while (!isCurToken(tokens, L_Keywords.L_End)) {
          words.push(tokens.shift() as string);
        }
        skip(tokens, L_Keywords.L_End);
        return new L_Nodes.SpecialNode(L_Keywords.RunKeyword, words.join());
      }
      default:
        throw Error();
    }
  } catch (error) {
    L_ParseErr(env, tokens, specialParse, index, start);
    throw error;
  }
}

function defParse(env: L_Env, tokens: string[]): L_Nodes.DefNode | L_Out {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, L_Keywords.DefKeywords);

    let commutative = false;
    if (isCurToken(tokens, L_Keywords.Commutative)) {
      skip(tokens, L_Keywords.Commutative);
      commutative = true;
    }

    // skip(tokens, L_Keywords.FunctionalStructuredFactOptPrefix);

    const opt: OptNode = optParse(env, tokens, false);

    let cond: ToCheckNode[] = [];
    if (isCurToken(tokens, ":")) {
      skip(tokens, ":");
      cond = factsArrParse(env, tokens, [L_Keywords.L_End], false);
    }

    const onlyIfs: ToCheckNode[] = [];
    if (isCurToken(tokens, "{")) {
      skip(tokens, "{");
      onlyIfs.push(...factsArrParse(env, tokens, ["}"], false));
      skip(tokens, "}");
    } else {
      skip(tokens, L_Keywords.L_End);
    }

    const out = new L_Nodes.DefNode(opt, cond, onlyIfs, commutative);

    if (defExec(env, out) === L_Structs.L_Out.True) return L_Out.True;
    else throw Error();
  } catch (error) {
    L_ParseErr(env, tokens, defParse, index, start);
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

      if (!optsVarsDeclaredInFacts(env, node.onlyIfs)) {
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
      ok = env.newDef(node.opt.optSymbol.name, node);
      // }
      for (const onlyIf of node.onlyIfs) {
        const ok = newFact(env, onlyIf);
        if (!ok) return env.errMesReturnBoolean(`Failed to store ${onlyIf}`);
      }
      return ok;
    }
  }
}

// function defExistParse(env: L_Env, tokens: string[]): L_Nodes.DefNode {
//   const start = tokens[0];
//   const index = tokens.length;

//   try {
//     skip(tokens, L_Keywords.def_exist);

//     let commutative = false;
//     if (isCurToken(tokens, L_Keywords.commutative)) {
//       skip(tokens, L_Keywords.commutative);
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
//       skip(tokens, ":");
//       cond = factsArrParse(env, tokens, [L_Keywords.L_End], false);
//     }

//     const onlyIfs: ToCheckNode[] = [];
//     if (isCurToken(tokens, "{")) {
//       skip(tokens, "{");
//       onlyIfs.push(...factsArrParse(env, tokens, ["}"], false));
//       skip(tokens, "}");
//     } else {
//       skip(tokens, L_Keywords.L_End);
//     }

//     return new L_Nodes.DefExistNode(opt, cond, onlyIfs, commutative, existVars);
//   } catch (error) {
//     L_ParseErr(env, tokens, defParse, index, start);
//     throw error;
//   }
// }

// --------------------------------------------------------
export function defCompositeParse(
  env: L_Env,
  tokens: string[]
): L_Nodes.DefCompositeNode | L_Out {
  const start = tokens[0];
  const index = tokens.length;

  try {
    let out: L_Nodes.DefCompositeNode | undefined = undefined;

    skip(tokens, L_Keywords.DefCompositeKeyword);
    const composite = slashCompositeParse(env, tokens);

    if (isCurToken(tokens, L_Keywords.L_End)) {
      skip(tokens, L_Keywords.L_End);
      out = new L_Nodes.DefCompositeNode(composite, []);
    } else {
      skip(tokens, ":");
      const facts: ToCheckNode[] = [];
      while (!isCurToken(tokens, L_Keywords.L_End)) {
        facts.push(
          ...factsArrParse(env, tokens, [",", L_Keywords.L_End], false)
        );
        if (isCurToken(tokens, ",")) skip(tokens, ",");
      }
      skip(tokens, L_Keywords.L_End);
      out = new L_Nodes.DefCompositeNode(composite, facts);
    }

    if (defCompositeExec(env, out) === L_Out.True) return L_Out.True;
    else throw Error();
  } catch (error) {
    L_ParseErr(env, tokens, defCompositeParse, index, start);
    throw error;
  }

  function defCompositeExec(env: L_Env, node: L_Nodes.DefCompositeNode): L_Out {
    try {
      if (!env.newCompositeVar(node.composite.name, node)) throw Error();
      return env.report(`[new def_composite] ${node}`);
    } catch {
      return L_Report.L_ReportErr(env, defCompositeExec, node);
    }
  }
}

export function isPropertyParse(
  env: L_Env,
  tokens: string[]
): L_Nodes.BuiltinCheckNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, L_Keywords.isPropertyKeyword);
    skip(tokens, "(");
    const name = skip(tokens);
    skip(tokens, ")");

    return new L_Nodes.IsPropertyNode(name, true);
  } catch (error) {
    L_ParseErr(env, tokens, isPropertyParse, index, start);
    throw error;
  }
}
export function orParse(
  env: L_Env,
  tokens: string[]
): L_Nodes.BuiltinCheckNode {
  throw Error();
}

export function isFormParse(
  env: L_Env,
  tokens: string[]
): L_Nodes.BuiltinCheckNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, L_Keywords.isFormKeyword);
    skip(tokens, "(");
    const given = symbolParse(env, tokens);
    skip(tokens, ",");
    const composite = slashCompositeParse(env, tokens);

    if (isCurToken(tokens, ",")) {
      skip(tokens, ",");
      skip(tokens, "{");
      const facts: ToCheckNode[] = [];
      while (!isCurToken(tokens, "}")) {
        facts.push(factParse(env, tokens));
        if (isCurToken(tokens, ",")) skip(tokens, ",");
      }
      skip(tokens, "}");
      skip(tokens, ")");
      return new L_Nodes.IsFormNode(given, composite, facts, true);
    } else {
      skip(tokens, ")");
      return new L_Nodes.IsFormNode(given, composite, [], true);
    }
  } catch (error) {
    L_ParseErr(env, tokens, isFormParse, index, start);
    throw error;
  }
}

function usePrecedenceToParseComposite(
  env: L_Env,
  tokens: string[],
  begin: string,
  end: string
): L_Structs.L_Symbol {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, begin);

    const precedenceMap = new Map<string, number>();
    precedenceMap.set("+", 0);
    precedenceMap.set("-", 0);
    precedenceMap.set("*", 1);
    precedenceMap.set("/", 1);

    let left = prefixSymbolParse(env, tokens);

    while (!isCurToken(tokens, end)) {
      const opt = tokens[0] as string;
      const next = getSymbolUntilPrecedenceIsNotHigher(
        env,
        tokens,
        end,
        precedenceMap.get(opt) as number,
        precedenceMap
      );
      left = new L_Structs.L_Composite(opt, [left, next]);
    }

    skip(tokens, end);
    return left as L_Structs.L_Symbol;
  } catch (error) {
    L_ParseErr(env, tokens, usePrecedenceToParseComposite, index, start);
    throw error;
  }

  function prefixSymbolParse(env: L_Env, tokens: string[]): L_Structs.L_Symbol {
    const start = tokens[0];
    const index = tokens.length;

    try {
      // TODO maybe is broken because it does not take # into consideration
      if (tokens[0] === L_Keywords.SlashKeyword) {
        return slashCompositeParse(env, tokens);
      } else {
        return singletonParse(env, tokens);
      }
    } catch (error) {
      L_ParseErr(env, tokens, prefixSymbolParse, index, start);
      throw error;
    }
  }

  function getSymbolUntilPrecedenceIsNotHigher(
    env: L_Env,
    tokens: string[],
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
      const opt = tokens[0] as string;
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

export function letsParse(env: L_Env, tokens: string[]): L_Nodes.LetsNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, L_Keywords.Lets);
    const name = skip(tokens);
    const regex = new RegExp(skipString(tokens));
    if (isCurToken(tokens, ":")) {
      skip(tokens, ":");
      const facts = factsArrParse(env, tokens, [L_Keywords.L_End], true);
      return new L_Nodes.LetsNode(name, regex, facts);
    } else {
      skip(tokens, L_Keywords.L_End);
      return new L_Nodes.LetsNode(name, regex, []);
    }
  } catch (error) {
    L_ParseErr(env, tokens, isFormParse, index, start);
    throw error;
  }
}

export function macroParse(env: L_Env, tokens: string[]): L_Nodes.MacroNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, L_Keywords.Macro);
    const name = skip(tokens);

    skip(tokens, '"');
    const macroTokens: string[] = [];
    while (!isCurToken(tokens, '"')) {
      macroTokens.push(skip(tokens));
    }
    skip(tokens, '"');

    skip(tokens, L_Keywords.L_End);
    const out = new L_Nodes.MacroNode(name, macroTokens);

    return out;
  } catch (error) {
    L_ParseErr(env, tokens, isFormParse, index, start);
    throw error;
  }
}

export function includeParse(
  env: L_Env,
  tokens: string[]
): L_Nodes.IncludeNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, L_Keywords.Include);

    skip(tokens, '"');
    let path: string = "";
    while (!isCurToken(tokens, '"')) {
      path += skip(tokens) as string;
    }
    skip(tokens, '"');

    skip(tokens, L_Keywords.L_End);
    const out = new L_Nodes.IncludeNode(path);

    return out;
  } catch (error) {
    L_ParseErr(env, tokens, isFormParse, index, start);
    throw error;
  }
}

export function defLiteralOperatorParse(
  env: L_Env,
  tokens: string[]
): L_Nodes.DefLiteralOptNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, L_Keywords.DefLiteralOperator);
    const name = skip(tokens);
    skip(tokens, "{");
    const path = skipString(tokens);
    skip(tokens, ",");
    const func = skipString(tokens);
    skip(tokens, "}");

    const vars = arrParse<L_Structs.L_Symbol>(
      env,
      tokens,
      symbolParse,
      undefined,
      [":", L_Keywords.L_End],
      false
    );

    if (isCurToken(tokens, L_Keywords.L_End)) {
      skip(tokens, L_Keywords.L_End);
      return new L_Nodes.DefLiteralOptNode(name, vars, [], path, func);
    } else {
      skip(tokens, ":");
      const facts = arrParse<ToCheckNode>(
        env,
        tokens,
        factParse,
        undefined,
        L_Keywords.L_End,
        false
      );
      skip(tokens, L_Keywords.L_End);
      return new L_Nodes.DefLiteralOptNode(name, vars, facts, path, func);
    }
  } catch (error) {
    L_ParseErr(env, tokens, isFormParse, index, start);
    throw error;
  }
}

export function symbolParse(env: L_Env, tokens: string[]): L_Structs.L_Symbol {
  const start = tokens[0];
  const index = tokens.length;

  try {
    let left = singleSymbolParse(env, tokens);
    while (env.getCompositeVar(tokens[0])) {
      const optName = skip(tokens);
      const right = singleSymbolParse(env, tokens);
      left = new L_Composite(optName, [left, right]);
    }
    return left;
  } catch (error) {
    L_ParseErr(env, tokens, isFormParse, index, start);
    throw error;
  }
}
