import {
  KnowNode,
  L_Node,
  LetNode,
  OrNode,
  OptNode,
  IfThenNode,
  DeclNode,
  DefDeclNode,
  IfThenDeclNode,
  FactNode,
  ByNode,
  ProveNode,
  ExistNode,
  HaveNode,
  AssumeByContraNode,
  OnlyIfDeclNode,
} from "./ast";
import { L_Env } from "./env";
import {
  KnowTypeKeywords,
  specialChars,
  StdStmtEnds,
  IfKeywords,
  DefKeywords,
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
    "@": knowParse,
    let: letParse,
    def: DeclNodeParse,
    ":": DeclNodeParse,
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
        break;
      }

      const func = KeywordFunctionMap[tokens[0]];
      if (func) {
        const node = func(env, tokens);
        holder.push(node);
        return node;
      } else {
        const nodes = optFactsParse(env, tokens, StdStmtEnds, true);
        nodes.forEach((e) => holder.push(e));
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
        const relParser: Function | undefined = factParserSignals[tokens[0]];
        if (relParser === undefined) {
          // out = OptParse(env, tokens);
          const outs: FactNode[] = optFactsParse(
            env,
            tokens,
            [...StdStmtEnds, ","],
            false
          );
          knowNode.facts = knowNode.facts.concat(outs);
        } else {
          //! THE FOLLOWING CODES ARE WRONG.
          let out: FactNode;
          out = relParser(env, tokens, true);
          knowNode.facts.push(out);
        }

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
        const facts = optFactsParse(env, tokens, StdStmtEnds, true);
        // const facts = listParse<FactNode>(
        //   env,
        //   tokens,
        //   singleOptParse,
        //   StdStmtEnds,
        //   true
        // );
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
      if (tokens.length >= 2 && tokens[1] === "(") {
        // parse functional operator
        const name: string = shiftVar(tokens);

        const vars: string[] = [];
        skip(tokens, "(");

        while (!isCurToken(tokens, ")")) {
          vars.push(shiftVar(tokens));
          if (isCurToken(tokens, ",")) skip(tokens, ",");
        }

        skip(tokens, ")");

        return new OptNode(name, vars);
      } else {
        // parse relational operator
        const vars: string[] = [];
        while (!IsKeywords.includes(tokens[0])) {
          vars.push(shiftVar(tokens));
          if (isCurToken(tokens, ",")) skip(tokens, ", ");
        }
        skip(tokens, IsKeywords);
        const name = shiftVar(tokens);
        return new OptNode(name, vars);
      }
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

      const vars = varLstParse(env, tokens, ["|", ...ThenKeywords], false);

      let req: FactNode[] = [];
      if (ThenKeywords.includes(tokens[0])) {
        skip(tokens, ThenKeywords);
      } else {
        skip(tokens, "|");
        // req = listParse<FactNode>(env, tokens, singleOptParse, ["=>", "then"], true);
        req = optFactsParse(env, tokens, ThenKeywords, true);
      }

      let onlyIfs: OptNode[];

      // const facts = listParse<FactNode>(env, tokens, singleOptParse, ends, skipEnd);
      const facts = optFactsParse(env, tokens, ends, skipEnd);
      if (facts.every((e) => e instanceof OptNode)) {
        onlyIfs = facts as OptNode[];
      } else {
        throw Error(`Not all onlyIfs are operator-type fact.`);
      }

      const out = new IfThenNode(vars, req, onlyIfs);
      return out;
    } catch (error) {
      handleParseError(env, "()=>{}", index, start);
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
      let nodeType = shiftVar(tokens);
      const name = shiftVar(tokens);

      if (L_Keywords.includes(name)) {
        env.newMessage(`Error: ${name} is a LiTeX keyword.`);
        throw Error();
      }

      if ([...IfKeywords, ...OnlyIfKeywords].includes(tokens[0])) {
        nodeType = shiftVar(tokens);
      }

      const vars = varLstParse(env, tokens, ["|"], true);

      // if (StdStmtEnds.includes(tokens[0])) {
      //   skip(tokens, StdStmtEnds);
      //   return new DefDeclNode(name, vars);
      // } else {
      //   skip(tokens, "|");
      // }

      // const req = listParse<FactNode>(
      //   env,
      //   tokens,
      //   singleOptParse,
      //   [...StdStmtEnds, "=>"],
      //   false
      // );
      const req = optFactsParse(env, tokens, [...StdStmtEnds, "=>"], false);

      let onlyIfs: FactNode[] = [];
      if (StdStmtEnds.includes(tokens[0])) {
        skip(tokens, StdStmtEnds);
      } else if (isCurToken(tokens, "=>")) {
        skip(tokens, "=>");

        // onlyIfs = listParse<FactNode>(
        //   env,
        //   tokens,
        //   singleOptParse,
        //   StdStmtEnds,
        //   true
        // );
        onlyIfs = optFactsParse(env, tokens, StdStmtEnds, true);
      }

      if (IfKeywords.includes(nodeType)) {
        return new IfThenDeclNode(name, vars, req, onlyIfs);
      } else if (DefKeywords.includes(nodeType)) {
        return new DefDeclNode(name, vars, req, onlyIfs);
      } else if (OnlyIfKeywords.includes(nodeType)) {
        return new OnlyIfDeclNode(name, vars, req, onlyIfs);
      }

      throw Error();
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
        toProve = ifThenParse(env, tokens, ["{"], false);
      } else {
        fixedIfThenOpt = OptParse(env, tokens);
      }

      const block: L_Node[] = [];
      skip(tokens, "{");
      while (tokens[0] !== "}") {
        while (["\n", ";"].includes(tokens[0])) {
          tokens.shift();
        }
        if (tokens[0] === "}") continue;

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
      const req = optFactsParse(env, tokens, [...StdStmtEnds], true);

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
        const facts = optFactsParse(env, tokens, StdStmtEnds, true);
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

  function optFactsParse(
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
        if (tokens.length >= 2 && tokens[1] === "(") {
          out.push(OptParse(env, tokens));
        } else {
          const vars: string[] = [];
          while (!IsAreKeywords.includes(tokens[0])) {
            vars.push(shiftVar(tokens));
            if (isCurToken(tokens, ",")) skip(tokens, ",");
          }
          const isAre = shiftVar(tokens);
          const optName = shiftVar(tokens);
          vars.forEach((e) => out.push(new OptNode(optName, [e])));
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
}
