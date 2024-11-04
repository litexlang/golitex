import {
  KnowNode,
  L_Node,
  LetNode,
  OptNode,
  IfThenNode,
  DeclNode,
  IffDeclNode,
  FactNode,
  ProveNode,
  ExistNode,
  HaveNode,
  OnlyIfDeclNode,
  LogicalOptNode,
  PostfixProve,
  IfThenDeclNode,
  LocalEnvNode,
  ReturnNode,
  ReturnExistNode,
  ByNode,
  OnlyIfNode,
  IffNode,
} from "./ast";
import { L_Env } from "./L_Env";
import {
  KnowTypeKeywords,
  StdStmtEnds,
  IfKeywords,
  LetKeywords,
  ThenKeywords,
  ProveKeywords,
  ExistKeywords,
  HaveKeywords,
  ProveByContradictionKeyword,
  OnlyIfKeywords,
  IsKeywords,
  IsAreKeywords,
  L_Keywords,
  IffKeywords,
  LogicalOptPairs,
  LogicalKeywords,
  PostfixProveKeywords,
  AreKeywords,
  DefKeywords,
  WhenKeyword,
  IffThenKeywords,
  OnlyIfThenKeywords,
  ContradictionKeyword,
  ReturnKeyword,
  ReturnExistKeyword,
  ByKeyword,
  DefByKeywords,
} from "./common";

export namespace L_Parser {
  function skip(tokens: string[], s: string | string[] = "") {
    if (typeof s === "string") {
      if (s === "") {
        return tokens.shift();
      } else if (s === tokens[0]) {
        return tokens.shift();
      } else {
        throw Error("unexpected symbol: " + tokens[0]);
      }
    } else {
      for (const value of s) {
        if (value === tokens[0]) {
          return tokens.shift();
        }
      }
      throw Error("unexpected symbol: " + tokens[0]);
    }
  }

  //! Not only gets symbol, in the future it will parse $$
  function shiftVar(tokens: string[]): string {
    const token = tokens.shift();
    if (typeof token !== "string") {
      throw new Error("No more tokens");
    }
    return token;
  }

  function isCurToken(tokens: string[], s: string) {
    return s === tokens[0];
  }

  function handleParseError(
    // tokens: string[],
    env: L_Env,
    m: string,
    index: number,
    start: string = ""
  ) {
    env.newMessage(`At ${start}[${index * -1}]: ${m}`);
  }

  export function parseUntilGivenEnd(
    env: L_Env,
    tokens: string[],
    end: string | null
  ): L_Node[] {
    try {
      let out: L_Node[] = [];

      if (end !== null) {
        while (!isCurToken(tokens, end)) {
          getNodesFromSingleNode(env, tokens, out);
        }
      } else {
        while (tokens.length !== 0) {
          getNodesFromSingleNode(env, tokens, out);
        }
      }

      return out;
    } catch (error) {
      env.newMessage(`Error: Syntax Error.`);
      throw error;
    }
  }

  const KeywordFunctionMap: {
    [key: string]: Function; // (env: L_Env, tokens: string[]) => any;
  } = {
    know: knowParse,
    let: letParse,
    "{": localEnvParse,
    // def: defineParse,
    def: yaDefineParse,
    prove: proveParse,
    prove_by_contradiction: proveParse,
    exist: existParse,
    have: haveParse,
    return: returnParse,
    return_exist: returnExistParse,
    by: byParse,
  };

  export function getNodesFromSingleNode(
    env: L_Env,
    tokens: string[],
    holder: L_Node[]
  ): void {
    const start = tokens[0];
    const index = tokens.length;
    try {
      while (tokens.length > 0) {
        while (tokens.length > 0 && StdStmtEnds.includes(tokens[0])) {
          tokens.shift();
        }
        if (tokens.length === 0) return;
        break;
      }

      const func = KeywordFunctionMap[tokens[0]];
      if (func) {
        const node = func(env, tokens);
        holder.push(node);
        return node;
      } else {
        const postProve = PostfixProveParse(env, tokens, StdStmtEnds, true);
        if (postProve.block.length === 0) {
          postProve.facts.forEach((e) => holder.push(e));
        } else {
          holder.push(postProve);
        }
      }
    } catch (error) {
      handleParseError(env, "node", index, start);
      throw error;
    }
  }

  function knowParse(env: L_Env, tokens: string[]): KnowNode {
    const start = tokens[0];
    const index = tokens.length;

    try {
      const knowNode: KnowNode = new KnowNode();

      skip(tokens, KnowTypeKeywords);
      while (!StdStmtEnds.includes(tokens[0])) {
        const outs: FactNode[] = factsParse(
          env,
          tokens,
          [...StdStmtEnds, ","],
          false
        );
        knowNode.facts = knowNode.facts.concat(outs);

        if (tokens[0] === ",") skip(tokens, ",");
        else break;
      }
      skip(tokens, StdStmtEnds);

      return knowNode;
    } catch (error) {
      handleParseError(env, "know", index, start);
      throw error;
    }
  }

  function letParse(env: L_Env, tokens: string[]): LetNode {
    const start = tokens[0];
    const index = tokens.length;

    try {
      skip(tokens, LetKeywords);
      const vars = listParse<string>(
        env,
        tokens,
        (env, e) => shiftVar(e),
        [...StdStmtEnds, "|"],
        false
      );

      if (!vars.every((e) => !L_Keywords.includes(e))) {
        env.newMessage(`Error: ${vars} contain LiTeX keywords.`);
        throw Error();
      }

      if (StdStmtEnds.includes(tokens[0])) {
        skip(tokens, StdStmtEnds);
        return new LetNode(vars, []);
      } else {
        skip(tokens, "|");
        const facts = factsParse(env, tokens, StdStmtEnds, true);
        return new LetNode(vars, facts);
      }
    } catch (error) {
      handleParseError(env, "let", index, start);
      throw error;
    }
  }

  function OptParse(env: L_Env, tokens: string[], parseNot: Boolean): OptNode {
    const start = tokens[0];
    const index = tokens.length;

    try {
      let name: string = "";
      let vars: string[] = [];
      let isT = true;

      if (parseNot) {
        while (tokens[0] === "not") {
          isT = false;
          skip(tokens, "not");
        }
      }

      if (tokens.length >= 2 && tokens[1] === "(") {
        // parse functional operator
        name = shiftVar(tokens);

        skip(tokens, "(");

        while (!isCurToken(tokens, ")")) {
          vars.push(shiftVar(tokens));
          if (isCurToken(tokens, ",")) skip(tokens, ",");
        }

        skip(tokens, ")");
      } else {
        const v = shiftVar(tokens);
        vars.push(v);
        skip(tokens, IsKeywords);
        name = shiftVar(tokens);
      }

      return new OptNode(name, vars, isT);
    } catch (error) {
      handleParseError(env, `${start} is invalid operator.`, index, start);
      throw error;
    }
  }

  function listParse<T>(
    env: L_Env,
    tokens: string[],
    parseFunc: (env: L_Env, tokens: string[], ...args: any[]) => T,
    end: string[],
    skipEnd: Boolean = true,
    separation: string = ","
  ): T[] {
    const start = tokens[0];
    const index = tokens.length;

    try {
      const out: T[] = [];
      while (!end.includes(tokens[0])) {
        out.push(parseFunc(env, tokens));
        if (isCurToken(tokens, separation)) skip(tokens, separation);
      }

      if (skipEnd) skip(tokens, end);

      return out;
    } catch (error) {
      handleParseError(env, "Parsing variables", index, start);
      throw error;
    }
  }

  function varLstParse(
    env: L_Env,
    tokens: string[],
    end: string[],
    skipEnd: Boolean = true,
    separation: string = ","
  ): string[] {
    const start = tokens[0];
    const index = tokens.length;

    try {
      const out: string[] = [];
      while (!end.includes(tokens[0])) {
        let curTok = shiftVar(tokens);
        out.push(curTok);
        if (isCurToken(tokens, separation)) skip(tokens, separation);
      }

      if (skipEnd) skip(tokens, end);

      return out;
    } catch (error) {
      handleParseError(env, "Parsing variables", index, start);
      throw error;
    }
  }

  function proveParse(env: L_Env, tokens: string[]): ProveNode {
    const start = tokens[0];
    const index = tokens.length;

    try {
      let byContradict = false;
      if (tokens[0] === ProveByContradictionKeyword) {
        byContradict = true;
        skip(tokens, ProveByContradictionKeyword);
      } else {
        skip(tokens, ProveKeywords);
      }

      let toProve: null | IfThenNode = null;
      let fixedIfThenOpt: null | OptNode = null;

      if (IfKeywords.includes(tokens[0])) {
        toProve = logicalOptParse(env, tokens);
      } else {
        fixedIfThenOpt = OptParse(env, tokens, true);
      }

      const block: L_Node[] = [];
      skip(tokens, "{");
      while (tokens[0] !== "}") {
        while (["\n", ";"].includes(tokens[0])) {
          tokens.shift();
        }
        if (tokens[0] === "}") break;

        getNodesFromSingleNode(env, tokens, block);
      }

      skip(tokens, "}");

      let contradict: OptNode | undefined = undefined;
      if (byContradict) {
        skip(tokens, ContradictionKeyword);
        contradict = OptParse(env, tokens, true);
        skip(tokens, StdStmtEnds);
      }

      if (toProve !== null) {
        return new ProveNode(toProve, null, block, contradict);
      } else {
        return new ProveNode(null, fixedIfThenOpt, block, contradict);
      }
    } catch (error) {
      handleParseError(env, "Parsing prove", index, start);
      throw error;
    }
  }

  function haveParse(env: L_Env, tokens: string[]): HaveNode {
    const start = tokens[0];
    const index = tokens.length;

    try {
      skip(tokens, HaveKeywords);
      const vars = listParse<string>(
        env,
        tokens,
        (env, e) => shiftVar(e),
        [...StdStmtEnds, "|"],
        false
      );

      if (!vars.every((e) => !L_Keywords.includes(e))) {
        env.newMessage(`Error: ${vars} contain LiTeX keywords.`);
        throw Error();
      }

      if (StdStmtEnds.includes(tokens[0])) {
        skip(tokens, StdStmtEnds);
        return new HaveNode(vars, []);
      } else {
        skip(tokens, "|");
        const facts: OptNode[] = [];

        while (!StdStmtEnds.includes(tokens[0])) {
          const fact = OptParse(env, tokens, true);
          facts.push(fact);
          if (isCurToken(tokens, ",")) skip(tokens, ",");
        }
        skip(tokens, StdStmtEnds);

        return new HaveNode(vars, facts);
      }
    } catch (error) {
      handleParseError(env, "have", index, start);
      throw error;
    }
  }

  // Main Function of parser
  function factsParse(
    env: L_Env,
    tokens: string[],
    end: string[],
    skipEnd: Boolean = false
  ): FactNode[] {
    const start = tokens[0];
    const index = tokens.length;

    try {
      const out: FactNode[] = [];
      while (!end.includes(tokens[0])) {
        let isT = true;
        if (isCurToken(tokens, "not")) {
          isT = false;
          skip(tokens, "not");
        }

        if (LogicalKeywords.includes(tokens[0])) {
          const fact = logicalOptParse(env, tokens);
          fact.isT = isT;
          out.push(fact);
        } else if (tokens.length >= 2 && tokens[1] === "(") {
          const fact = OptParse(env, tokens, false); // false: When using factsParse, not prefix are already removed.
          fact.isT = isT;
          out.push(fact);
        } else {
          const vars: string[] = [];
          while (!IsAreKeywords.includes(tokens[0])) {
            vars.push(shiftVar(tokens));
            if (isCurToken(tokens, ",")) skip(tokens, ",");
          }
          const isAre = skip(tokens, IsAreKeywords) as string;
          if (AreKeywords.includes(isAre)) {
            if (vars.length < 2) {
              handleParseError(
                env,
                "`are` requires more than 1 parameters.",
                index,
                start
              );
              throw Error();
            }
          } else {
            if (vars.length !== 1) {
              handleParseError(
                env,
                "`is` requires exactly one parameter.",
                index,
                start
              );
              throw Error();
            }
          }

          const optName = shiftVar(tokens);
          for (const v of vars) {
            const fact = new OptNode(optName, [v]);
            fact.isT = isT;
            out.push(fact);
          }
        }

        if (isCurToken(tokens, ",")) skip(tokens, ",");
      }

      if (skipEnd) skip(tokens, end);

      return out;
    } catch (error) {
      handleParseError(env, "fact", index, start);
      throw error;
    }
  }

  function logicalOptParse(
    env: L_Env,
    tokens: string[]
    // ends: string[] = StdStmtEnds,
    // skipEnd = true
  ): LogicalOptNode {
    const start = tokens[0];
    const index = tokens.length;

    try {
      const type = skip(tokens, [
        ...IfKeywords,
        ...OnlyIfKeywords,
        ...IffKeywords,
      ]);
      if (type === undefined) throw Error();
      const separation = LogicalOptPairs[type];

      const symbolsBeforeThenKeyword: string[] = [];
      for (let i = 0; i < tokens.length; i++) {
        if (!separation.includes(tokens[i]))
          symbolsBeforeThenKeyword.push(tokens[i]);
        else break;
      }

      let vars: string[] = [];
      let req: FactNode[] = [];
      if (symbolsBeforeThenKeyword.includes("|")) {
        vars = varLstParse(env, tokens, ["|"], false);
        skip(tokens, "|");

        req = factsParse(env, tokens, separation, true);
      } else {
        req = factsParse(env, tokens, separation, true);
      }

      skip(tokens, "{");

      const onlyIfs = factsParse(env, tokens, ["}"], true);

      let byName: string | undefined = undefined;

      if (isCurToken(tokens, "[")) {
        skip(tokens, "[");
        byName = shiftVar(tokens);
        skip(tokens, "]");
      }

      if (IfKeywords.includes(type)) {
        const out = new IfThenNode(vars, req, onlyIfs, true, byName);
        return out;
      } else if (OnlyIfKeywords.includes(type)) {
        const out = new OnlyIfNode(vars, req, onlyIfs, true, byName);
        return out;
      } else if (IffKeywords.includes(type)) {
        const out = new IffNode(vars, req, onlyIfs, true, byName);
        return out;
      }

      throw Error();
    } catch (error) {
      handleParseError(env, "if-then", index, start);
      throw error;
    }
  }

  function PostfixProveParse(
    env: L_Env,
    tokens: string[],
    end: string[],
    skipEnd: Boolean = false
  ): PostfixProve {
    const start = tokens[0];
    const index = tokens.length;

    try {
      const facts = factsParse(env, tokens, [...end, ...PostfixProveKeywords]);
      const block: L_Node[] = [];
      if (PostfixProveKeywords.includes(tokens[0])) {
        skip(tokens, PostfixProveKeywords);
        skip(tokens, "{");
        while (tokens[0] !== "}") {
          while (["\n", ";"].includes(tokens[0])) {
            tokens.shift();
          }
          if (tokens[0] === "}") break;

          getNodesFromSingleNode(env, tokens, block);
        }
        skip(tokens, "}");
      }

      if (skipEnd) skip(tokens, end);

      return new PostfixProve(facts, block);
    } catch (error) {
      handleParseError(env, "fact", index, start);
      throw error;
    }
  }

  function yaDefineParse(env: L_Env, tokens: string[]): DeclNode {
    const start = tokens[0];
    const index = tokens.length;

    try {
      skip(tokens, DefKeywords);

      const opt: OptNode = OptParse(env, tokens, false);
      const separator = shiftVar(tokens);

      skip(tokens, "{");
      const onlyIfs = factsParse(
        env,
        tokens,
        StdStmtEnds.concat(WhenKeyword).concat(["}"]),
        false
      );
      skip(tokens, "}");

      let req: FactNode[] = [];
      if (tokens[0] === WhenKeyword) {
        skip(tokens, WhenKeyword);
        req = factsParse(env, tokens, StdStmtEnds, false);
      }

      let byName: undefined | string = undefined;
      if (isCurToken(tokens, "[")) {
        skip(tokens, "[");
        byName = shiftVar(tokens);
        skip(tokens, "]");
      }

      skip(tokens, StdStmtEnds);

      if (ThenKeywords.includes(separator)) {
        return new IfThenDeclNode(opt.fullName, opt.vars, req, onlyIfs, byName);
      } else if (IffThenKeywords.includes(separator)) {
        return new IffDeclNode(opt.fullName, opt.vars, req, onlyIfs, byName);
      } else if (OnlyIfThenKeywords.includes(separator)) {
        return new OnlyIfDeclNode(opt.fullName, opt.vars, req, onlyIfs, byName);
      }

      throw Error();
    } catch (error) {
      handleParseError(env, "define", index, start);
      throw error;
    }
  }

  function defineParse(env: L_Env, tokens: string[]): DeclNode {
    const start = tokens[0];
    const index = tokens.length;

    try {
      skip(tokens, DefKeywords);

      let byName: undefined | string = undefined;
      if (isCurToken(tokens, "[")) {
        skip(tokens, "[");
        byName = shiftVar(tokens);
        skip(tokens, "]");
      }

      const opt: OptNode = OptParse(env, tokens, false);
      const separator = shiftVar(tokens);

      const onlyIfs = factsParse(
        env,
        tokens,
        StdStmtEnds.concat(WhenKeyword),
        false
      );

      let req: FactNode[] = [];
      if (tokens[0] === WhenKeyword) {
        skip(tokens, WhenKeyword);
        req = factsParse(env, tokens, StdStmtEnds, false);
      }

      skip(tokens, StdStmtEnds);

      if (ThenKeywords.includes(separator)) {
        return new IfThenDeclNode(opt.fullName, opt.vars, req, onlyIfs, byName);
      } else if (IffThenKeywords.includes(separator)) {
        return new IffDeclNode(opt.fullName, opt.vars, req, onlyIfs, byName);
      } else if (OnlyIfThenKeywords.includes(separator)) {
        return new OnlyIfDeclNode(opt.fullName, opt.vars, req, onlyIfs, byName);
      }

      throw Error();
    } catch (error) {
      handleParseError(env, "fact", index, start);
      throw error;
    }
  }

  function localEnvParse(env: L_Env, tokens: string[]): LocalEnvNode {
    const start = tokens[0];
    const index = tokens.length;

    try {
      skip(tokens, "{");
      const nodes = parseUntilGivenEnd(env, tokens, "}");
      skip(tokens, "}");
      const out = new LocalEnvNode(nodes);
      return out;
    } catch (error) {
      handleParseError(env, "{}", index, start);
      throw error;
    }
  }

  function returnParse(env: L_Env, tokens: string[]): ReturnNode {
    const start = tokens[0];
    const index = tokens.length;

    try {
      skip(tokens, ReturnKeyword);
      const facts = factsParse(env, tokens, StdStmtEnds, true);
      return new ReturnNode(facts);
    } catch (error) {
      handleParseError(env, "return/so", index, start);
      throw error;
    }
  }

  function returnExistParse(env: L_Env, tokens: string[]): ReturnExistNode {
    const start = tokens[0];
    const index = tokens.length;

    try {
      skip(tokens, ReturnExistKeyword);
      const names: string[] = [];
      while (StdStmtEnds.includes(tokens[0])) {
        names.push(shiftVar(tokens));
        if (isCurToken(tokens, ",")) {
          skip(tokens, ",");
        }
      }

      return new ReturnExistNode(names);
    } catch (error) {
      handleParseError(env, "return_exist", index, start);
      throw error;
    }
  }

  function existParse(env: L_Env, tokens: string[]): ExistNode {
    const start = tokens[0];
    const index = tokens.length;

    try {
      skip(tokens, ExistKeywords);
      const facts: OptNode[] = [];

      while (!StdStmtEnds.includes(tokens[0])) {
        const fact = OptParse(env, tokens, true);
        facts.push(fact);
        if (isCurToken(tokens, ",")) skip(tokens, ",");
      }
      skip(tokens, StdStmtEnds);

      return new ExistNode(facts);
    } catch (error) {
      handleParseError(env, "Exist prove", index, start);
      throw error;
    }
  }

  function byParse(env: L_Env, tokens: string[]): ByNode {
    const start = tokens[0];
    const index = tokens.length;

    try {
      skip(tokens, ByKeyword);
      const byName = shiftVar(tokens);
      skip(tokens, "(");
      const vars: string[] = [];
      while (!isCurToken(tokens, ")")) {
        vars.push(shiftVar(tokens));
        if (isCurToken(tokens, ",")) skip(tokens, ",");
      }
      skip(tokens, ")");

      return new ByNode(byName, vars);
    } catch (error) {
      handleParseError(env, "by", index, start);
      throw error;
    }
  }
}
