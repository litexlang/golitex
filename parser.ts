import {
  KnowNode,
  L_Node,
  LetNode,
  OrNode,
  OptNode,
  IfThenNode,
  DeclNode,
  IffDeclNode,
  FactNode,
  ProveNode,
  ExistNode,
  HaveNode,
  AssumeByContraNode,
  OnlyIfDeclNode,
  LogicalOptNode,
  ByNode,
} from "./ast";
import { L_Env } from "./env";
import {
  KnowTypeKeywords,
  StdStmtEnds,
  IfKeywords,
  LetKeywords,
  ThenKeywords,
  ProveKeywords,
  ExistKeywords,
  HaveKeywords,
  AssumeByContraKeywords,
  OnlyIfKeywords,
  IsKeywords,
  IsAreKeywords,
  NotKeywords,
  OrKeywords,
  L_Keywords,
  IffKeywords,
  LogicalOptPairs,
  LogicalKeywords,
  ByKeywords,
  AreKeywords,
} from "./common";

export namespace parser {
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

  export function L_StmtsParse(env: L_Env, tokens: string[]): L_Node[] {
    try {
      const result: L_Node[] = [];
      getNodesFromSingleNode(env, tokens, result);
      return result;
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
    def: DeclNodeParse,
    prove: proveParse,
    exist: existParse,
    have: haveParse,
    assume_by_contradiction: assumeByContraParse,
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
        const byNode = byFactsParse(env, tokens, StdStmtEnds, true);
        if (byNode.block.length === 0) {
          byNode.facts.forEach((e) => holder.push(e));
        } else {
          holder.push(byNode);
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

  const factParserSignals: { [key: string]: Function } = {
    or: orParse,
    not: notParse,
    if: ifThenParse,
    "?": ifThenParse,
  };

  function singleOptParse(env: L_Env, tokens: string[]): FactNode {
    const start = tokens[0];
    const index = tokens.length;

    try {
      const relParser: Function | undefined = factParserSignals[tokens[0]];
      let out: FactNode;
      if (relParser === undefined) {
        out = OptParse(env, tokens);
      } else {
        out = relParser(env, tokens);
      }

      return out;
    } catch (error) {
      handleParseError(env, "fact", index, start);
      throw error;
    }
  }

  function OptParse(env: L_Env, tokens: string[]): OptNode {
    const start = tokens[0];
    const index = tokens.length;

    try {
      let name: string = "";
      let vars: string[] = [];
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
        // parse relational operator
        while (!IsKeywords.includes(tokens[0])) {
          vars.push(shiftVar(tokens));
          if (isCurToken(tokens, ",")) skip(tokens, ", ");
        }
        skip(tokens, IsKeywords);
        name = shiftVar(tokens);
      }

      return new OptNode(name, vars);
    } catch (error) {
      handleParseError(env, `${start} is invalid operator.`, index, start);
      throw error;
    }
  }

  // At parsing stage, not is "executed"
  function notParse(env: L_Env, tokens: string[]): FactNode {
    const start = tokens[0];
    const index = tokens.length;

    try {
      skip(tokens, NotKeywords);
      const fact = singleOptParse(env, tokens);
      fact.isT = false;
      return fact;
    } catch (error) {
      handleParseError(env, "not", index, start);
      throw error;
    }
  }

  function orParse(env: L_Env, tokens: string[]): OrNode {
    const start = tokens[0];
    const index = tokens.length;

    try {
      skip(tokens, OrKeywords);

      skip(tokens, "{");

      const facts: FactNode[] = [];
      while (!isCurToken(tokens, "}")) {
        facts.push(singleOptParse(env, tokens));
        if (isCurToken(tokens, ",")) skip(tokens, ",");
      }

      skip(tokens, "}");
      return new OrNode(facts);
    } catch (error) {
      handleParseError(env, "or", index, start);
      throw error;
    }
  }

  function ifThenParse(
    env: L_Env,
    tokens: string[],
    ends: string[] = StdStmtEnds,
    skipEnd = true
  ): IfThenNode {
    const start = tokens[0];
    const index = tokens.length;

    try {
      skip(tokens, IfKeywords);

      const symbolsBeforeThenKeyword: string[] = [];
      for (let i = 0; i < tokens.length; i++) {
        if (!ThenKeywords.includes(tokens[i]))
          symbolsBeforeThenKeyword.push(tokens[i]);
        else break;
      }

      let vars: string[] = [];
      let req: FactNode[] = [];
      if (symbolsBeforeThenKeyword.includes("|")) {
        vars = varLstParse(env, tokens, ["|"], false);
        skip(tokens, "|");
        req = factsParse(env, tokens, ThenKeywords, true);
      } else {
        req = factsParse(env, tokens, ThenKeywords, true);
      }

      let onlyIfs: OptNode[];
      const facts = factsParse(env, tokens, StdStmtEnds, skipEnd);
      if (facts.every((e) => e instanceof OptNode)) {
        onlyIfs = facts as OptNode[];
      } else {
        throw Error(`Not all onlyIfs are operator-type fact.`);
      }

      const out = new IfThenNode(vars, req, onlyIfs);
      return out;
    } catch (error) {
      handleParseError(env, "if-then", index, start);
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

  function DeclNodeParse(env: L_Env, tokens: string[]): DeclNode {
    const start = tokens[0];
    const index = tokens.length;
    try {
      shiftVar(tokens);
      const name = shiftVar(tokens);

      if (L_Keywords.includes(name)) {
        env.newMessage(`Error: ${name} is a LiTeX keyword.`);
        throw Error();
      }

      if (
        [...IfKeywords, ...IffKeywords, ...OnlyIfKeywords].includes(tokens[0])
      ) {
        const logicalOpt = logicalOptParse(env, tokens, StdStmtEnds, true);
        return DeclNode.create(name, logicalOpt);
        // return new IfThenDeclNode(
        //   name,
        //   ifThen.vars,
        //   ifThen.req,
        //   ifThen.onlyIfs
        // );
      } else {
        let type = "";
        if (LogicalKeywords.includes(tokens[0])) {
          type = shiftVar(tokens);
        }

        let req: FactNode[] = [];
        // `|` must exist in declaration to reduce confusion.
        const vars = varLstParse(env, tokens, ["|"], false);

        skip(tokens, "|");
        req = factsParse(env, tokens, [...StdStmtEnds], false);

        skip(tokens, StdStmtEnds);

        if (IffKeywords.includes(type)) {
          return new IffDeclNode(name, vars, req, []);
        } else if (OnlyIfKeywords.includes(type)) {
          return new OnlyIfDeclNode(name, vars, req, []);
        } else {
          return new IffDeclNode(name, vars, req, []);
        }
      }

      // if (IfKeywords.includes(nodeType)) {
      //   return new IfThenDeclNode(name, vars, req, onlyIfs);
      // } else if (DefKeywords.includes(nodeType)) {
      //   return new IffDeclNode(name, vars, req, onlyIfs);
      // } else if (OnlyIfKeywords.includes(nodeType)) {
      //   return new OnlyIfDeclNode(name, vars, req, onlyIfs);
      // }
    } catch (error) {
      handleParseError(env, "Parsing variables", index, start);
      throw error;
    }
  }

  function proveParse(env: L_Env, tokens: string[]): ProveNode {
    const start = tokens[0];
    const index = tokens.length;

    try {
      skip(tokens, ProveKeywords);

      let toProve: null | IfThenNode = null;
      let fixedIfThenOpt: null | OptNode = null;

      if (IfKeywords.includes(tokens[0])) {
        toProve = logicalOptParse(env, tokens, ["{"], false);
      } else {
        fixedIfThenOpt = OptParse(env, tokens);
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

      if (toProve !== null) {
        return new ProveNode(toProve, null, block);
      } else {
        return new ProveNode(null, fixedIfThenOpt, block);
      }
    } catch (error) {
      handleParseError(env, "Parsing prove", index, start);
      throw error;
    }
  }

  function existParse(env: L_Env, tokens: string[]): ExistNode {
    const start = tokens[0];
    const index = tokens.length;

    try {
      skip(tokens, ExistKeywords);
      const name = shiftVar(tokens);
      const vars = varLstParse(env, tokens, ["|", ...StdStmtEnds], false);

      if (StdStmtEnds.includes(tokens[0])) {
        skip(tokens, StdStmtEnds);
        return new ExistNode(name, vars, []);
      } else {
        skip(tokens, "|");
      }

      // const req = listParse<FactNode>(
      //   env,
      //   tokens,
      //   singleOptParse,
      //   [...StdStmtEnds],
      //   true
      // );
      const req = factsParse(env, tokens, [...StdStmtEnds], true);

      return new ExistNode(name, vars, req);
    } catch (error) {
      handleParseError(env, "Exist prove", index, start);
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
        // const facts = listParse<FactNode>(
        //   env,
        //   tokens,
        //   singleOptParse,
        //   StdStmtEnds,
        //   true
        // );
        const facts = factsParse(env, tokens, StdStmtEnds, true);
        return new HaveNode(vars, facts);
      }
    } catch (error) {
      handleParseError(env, "have", index, start);
      throw error;
    }
  }

  function assumeByContraParse(
    env: L_Env,
    tokens: string[]
  ): AssumeByContraNode {
    const start = tokens[0];
    const index = tokens.length;

    try {
      skip(tokens, AssumeByContraKeywords);
      const assume = singleOptParse(env, tokens);
      skip(tokens, "{");
      const block: L_Node[] = [];
      while (!isCurToken(tokens, "}")) {
        getNodesFromSingleNode(env, tokens, block);
      }
      skip(tokens, "}");
      skip(tokens, "{");
      const contradict = singleOptParse(env, tokens);
      skip(tokens, "}");
      return new AssumeByContraNode(assume, block, contradict);
    } catch (error) {
      handleParseError(env, "assume_by_contradiction", index, start);
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
          const fact = logicalOptParse(
            env,
            tokens,
            [",", ...StdStmtEnds],
            false
          );
          fact.isT = isT;
          out.push(fact);
        } else if (tokens.length >= 2 && tokens[1] === "(") {
          const fact = OptParse(env, tokens);
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
    tokens: string[],
    ends: string[] = StdStmtEnds,
    skipEnd = true
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

      let onlyIfs: OptNode[] = [];
      const facts = factsParse(env, tokens, ends, skipEnd);

      if (facts.every((e) => e instanceof OptNode)) {
        onlyIfs = facts as OptNode[];
      } else {
        // throw Error(`Not all onlyIfs are operator-type fact.`);
      }

      const out = LogicalOptNode.create(type, vars, req, onlyIfs);
      return out;
    } catch (error) {
      handleParseError(env, "if-then", index, start);
      throw error;
    }
  }

  function byFactsParse(
    env: L_Env,
    tokens: string[],
    end: string[],
    skipEnd: Boolean = false
  ): ByNode {
    const start = tokens[0];
    const index = tokens.length;

    try {
      const facts = factsParse(env, tokens, [...end, ...ByKeywords]);
      const block: L_Node[] = [];
      if (ByKeywords.includes(tokens[0])) {
        skip(tokens, ByKeywords);
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

      return new ByNode(facts, block);
    } catch (error) {
      handleParseError(env, "fact", index, start);
      throw error;
    }
  }
}
