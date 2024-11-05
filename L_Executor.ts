import {
  KnowNode,
  L_Node,
  LetNode,
  FactNode,
  DeclNode,
  ProveNode,
  HaveNode,
  PostfixProve,
  IfThenNode,
  OptNode,
  LocalEnvNode,
  ReturnNode,
  ExistNode,
  ReturnExistNode,
  ByNode,
} from "./ast";
import { L_Env } from "./L_Env";
import { L_Checker } from "./L_Checker";
import { L_FactStorage, StoredFact, StoredReq } from "./L_FactStorage";

export enum RType {
  Error,
  True,
  False,
  Unknown,
}

export const RTypeMap: { [key in RType]: string } = {
  [RType.Error]: "error",
  [RType.False]: "check: false",
  [RType.True]: "check: true",
  [RType.Unknown]: "check: unknown",
};

function successMesIntoEnv(env: L_Env, node: L_Node): RType {
  env.newMessage(`OK! ${node.toString()}`);
  return RType.True;
}

export namespace L_Executor {
  const nodeExecMap: { [key: string]: (env: L_Env, node: any) => RType } = {
    IffDeclNode: declExec,
    IfThenDeclNode: declExec,
    ExistNode: existExec,
    OnlyIfDeclNode: declExec,
    KnowNode: knowExec,
    LetNode: letExec,
    ProveNode: proveExec,
    HaveNode: haveExec,
    PostfixProve: PostfixProve,
    LocalEnvNode: localEnvExec,
    ReturnNode: returnExec,
    ReturnExistNode: returnExistExec,
    ByNode: byExec,
  };

  export function nodeExec(env: L_Env, node: L_Node, showMsg = true): RType {
    try {
      const nodeType = node.constructor.name;
      const execFunc = nodeExecMap[nodeType];

      if (execFunc && execFunc(env, node) === RType.True)
        return successMesIntoEnv(env, node);
      else if (node instanceof FactNode) {
        try {
          const out = factExec(env, node as FactNode);

          if (out === RType.True && showMsg) {
            env.newMessage(`OK! ${node}`);
          } else if (out === RType.Unknown) {
            env.newMessage(`Unknown ${node}`);
          } else if (out === RType.Error) {
            env.newMessage(`Error ${node}`);
          }
          return out;
        } catch (error) {
          throw Error(`${node as FactNode}`);
        }
      }
      return RType.Error;
    } catch (error) {
      if (error instanceof Error) env.newMessage(`Error: ${error.message}`);
      return RType.Error;
    }
  }

  function haveExec(env: L_Env, node: HaveNode): RType {
    try {
      for (const e of node.vars) {
        const ok = env.safeNewVar(e);
        if (!ok) return RType.Error;
      }

      for (const fact of node.facts) {
        if (!env.inHaves(fact.fullName)) {
          env.newMessage(`Not every existence of given fact is validated.`);
          return RType.Error;
        }
      }

      for (const fact of node.facts) {
        if (node.vars.every((e) => !fact.vars.includes(e))) {
          env.newMessage(
            `${fact} does not include any newly declared variable.`
          );
          return RType.Error;
        }
        L_FactStorage.store(env, fact);
      }

      return RType.True;
    } catch (error) {
      env.newMessage(`Error: ${node.toString()}`);
      return RType.Error;
    }
  }

  function letExec(env: L_Env, node: LetNode): RType {
    try {
      for (const e of node.vars) {
        const ok = env.safeNewVar(e);
        if (!ok) return RType.Error;
      }
      // node.vars.forEach((e) => env.newVar(e, e));

      for (const f of node.facts) L_FactStorage.store(env, f, []);

      for (const f of node.facts) {
        if (f instanceof IfThenNode) {
          L_FactStorage.storeIfThenBy(env, f, new StoredFact([], [], true));
        }
      }

      return RType.True;
    } catch (error) {
      env.newMessage(`Error: ${node.toString()}`);
      return RType.Error;
    }
  }

  export function knowExec(env: L_Env, node: KnowNode): RType {
    try {
      for (const fact of node.facts) L_FactStorage.store(env, fact, []);
      for (const fact of node.facts) {
        if (fact instanceof IfThenNode) {
          L_FactStorage.storeIfThenBy(env, fact, new StoredFact([], [], true));
        }
      }
      return RType.True;
    } catch (error) {
      let m = `'${node.toString()}'`;
      if (error instanceof Error) m += ` ${error.message}`;
      env.newMessage(m);
      throw error;
    }
  }

  function declExec(env: L_Env, node: DeclNode): RType {
    try {
      const ok = env.safeDeclOpt(node.name, node);
      if (!ok) return RType.Error;

      L_FactStorage.declNewFact(env, node);

      return RType.True;
    } catch (error) {
      let m = `'${node.toString()}'`;
      if (error instanceof Error) m += ` ${error.message}`;
      env.newMessage(m);
      throw error;
    }
  }

  function proveExec(env: L_Env, node: ProveNode): RType {
    if (node.contradict === undefined) {
      if (node.toProve !== null) {
        return proveIfThen(env, node.toProve, node.block);
      } else {
        return proveOpt(env, node.fixedIfThenOpt as OptNode, node.block);
      }
    } else {
      if (node.toProve !== null) {
        env.newMessage(
          `At current version, you can not prove if-then by contradiction.`
        );
        return RType.Error;
      } else {
        return proveOptByContradict(
          env,
          node.fixedIfThenOpt as OptNode,
          node.block,
          node.contradict as OptNode
        );
      }
    }
  }

  function proveIfThen(
    env: L_Env,
    toProve: IfThenNode,
    block: L_Node[]
  ): RType {
    try {
      const newEnv = new L_Env(env);
      for (const v of toProve.vars) {
        const ok = newEnv.safeNewVar(v);
        if (!ok) throw Error();
      }

      for (const fact of toProve.req) {
        const ok = L_FactStorage.store(newEnv, fact, []);
        if (!ok) throw Error();
      }

      for (const subNode of block) {
        const out = nodeExec(newEnv, subNode, false);
        if (out === RType.Error) {
          newEnv.getMessages().forEach((e) => env.newMessage(e));
          env.newMessage(`Errors: Failed to execute ${subNode}`);
          return RType.Error;
        }
      }

      if (newEnv.someVarsDeclaredHere(toProve, [])) {
        newEnv.getMessages().forEach((e) => env.newMessage(e));
        env.newMessage(
          `Error: Some variables in ${toProve} are declared in block. It's illegal to declare operator or variable with the same name in the if-then expression you want to prove.`
        );
        return RType.Error;
      }

      if (newEnv.someOptsDeclaredHere(toProve)) {
        newEnv.getMessages().forEach((e) => env.newMessage(e));
        env.newMessage(
          `Error: Some operators in ${toProve} are declared in block. It's illegal to declare operator or variable with the same name in the if-then expression you want to prove.`
        );
        return RType.Error;
      }

      for (const toCheck of toProve.onlyIfs) {
        const out = nodeExec(newEnv, toCheck, false);
        if (out !== RType.True) return out;
      }

      L_FactStorage.store(env, toProve, []);

      return RType.True;
    } catch (error) {
      env.newMessage(`Error: ${toProve}`);
      return RType.Error;
    }
  }

  function proveOpt(env: L_Env, toProve: OptNode, block: L_Node[]): RType {
    try {
      const newEnv = new L_Env(env);

      for (const subNode of block) {
        const out = nodeExec(newEnv, subNode, false);
        if (out === RType.Error) {
          newEnv.getMessages().forEach((e) => env.newMessage(e));
          env.newMessage(`Errors: Failed to execute ${subNode}`);
          return RType.Error;
        }
      }

      if (newEnv.someVarsDeclaredHere(toProve, [])) {
        newEnv.getMessages().forEach((e) => env.newMessage(e));
        env.newMessage(
          `Error: Some variables in ${toProve} are declared in block. It's illegal to declare operator or variable with the same name in the if-then expression you want to prove.`
        );
        return RType.Error;
      }

      if (newEnv.someOptsDeclaredHere(toProve)) {
        newEnv.getMessages().forEach((e) => env.newMessage(e));
        env.newMessage(
          `Error: Some operators in ${toProve} are declared in block. It's illegal to declare operator or variable with the same name in the if-then expression you want to prove.`
        );
        return RType.Error;
      }

      const out = L_Checker.check(newEnv, toProve);
      if (out !== RType.True) return out;

      L_FactStorage.store(env, toProve, []);

      return RType.True;
    } catch {
      env.newMessage(`${toProve}`);
      return RType.Error;
    }
  }

  function proveOptByContradict(
    env: L_Env,
    toProve: OptNode,
    block: L_Node[],
    contradict: OptNode
  ): RType {
    try {
      const newEnv = new L_Env(env);

      toProve.isT = !toProve.isT;
      L_FactStorage.store(newEnv, toProve, []);

      for (const subNode of block) {
        const out = nodeExec(newEnv, subNode, false);
        if (out === RType.Error) {
          newEnv.getMessages().forEach((e) => env.newMessage(e));
          env.newMessage(`Errors: Failed to execute ${subNode}`);
          return RType.Error;
        }
      }

      let out = L_Checker.check(newEnv, contradict);
      if (out !== RType.True) {
        env.newMessage(`Errors: Failed to execute ${contradict}`);
        return RType.Error;
      }

      contradict.isT = !contradict.isT;
      out = L_Checker.check(newEnv, contradict);
      if (out !== RType.True) {
        env.newMessage(`Errors: Failed to execute ${contradict}`);
        return RType.Error;
      }

      if (newEnv.someVarsDeclaredHere(toProve, [])) {
        newEnv.getMessages().forEach((e) => env.newMessage(e));
        env.newMessage(
          `Error: Some variables in ${toProve} are declared in block. It's illegal to declare operator or variable with the same name in the if-then expression you want to prove.`
        );
        return RType.Error;
      }

      if (newEnv.someOptsDeclaredHere(toProve)) {
        newEnv.getMessages().forEach((e) => env.newMessage(e));
        env.newMessage(
          `Error: Some operators in ${toProve} are declared in block. It's illegal to declare operator or variable with the same name in the if-then expression you want to prove.`
        );
        return RType.Error;
      }

      toProve.isT = !toProve.isT;
      L_FactStorage.store(env, toProve, []);

      return RType.True;
    } catch {
      env.newMessage(`${toProve}`);
      return RType.Error;
    }
  }

  function PostfixProve(env: L_Env, PostfixProve: PostfixProve): RType {
    try {
      const newEnv = new L_Env(env);
      for (const subNode of PostfixProve.block) {
        const out = nodeExec(newEnv, subNode, false);
        if (out !== RType.True) {
          newEnv.getMessages().forEach((e) => env.newMessage(e));
          env.newMessage(`${PostfixProve} failed.`);
          return out;
        }
      }

      for (const fact of PostfixProve.facts) {
        if (newEnv.someVarsDeclaredHere(fact, [])) {
          newEnv.getMessages().forEach((e) => env.newMessage(e));
          env.newMessage(
            `Error: Some variables in ${fact} are declared in block. It's illegal to declare operator or variable with the same name in the if-then expression you want to prove.`
          );
          return RType.Error;
        }

        if (newEnv.someOptsDeclaredHere(fact)) {
          newEnv.getMessages().forEach((e) => env.newMessage(e));
          env.newMessage(
            `Error: Some operators in ${fact} are declared in block. It's illegal to declare operator or variable with the same name in the if-then expression you want to prove.`
          );
          return RType.Error;
        }
      }

      for (const fact of PostfixProve.facts) {
        const out = L_Checker.check(newEnv, fact);
        if (out !== RType.True) {
          newEnv.getMessages().forEach((e) => env.newMessage(e));
          env.newMessage(`${PostfixProve} failed.`);
          return out;
        }
      }

      for (const fact of PostfixProve.facts) {
        L_FactStorage.store(env, fact, []);
      }

      return RType.True;
    } catch (error) {
      env.newMessage("by error");
      return RType.Error;
    }
  }

  function factExec(env: L_Env, toCheck: FactNode): RType {
    try {
      if (!(toCheck.varsDeclared(env, []) && toCheck.factsDeclared(env))) {
        return RType.Error;
      }

      let out = L_Checker.check(env, toCheck);
      if (out === RType.True) {
        L_FactStorage.store(env, toCheck, []);
      }

      if (toCheck instanceof IfThenNode) {
        L_FactStorage.storeIfThenBy(env, toCheck, new StoredFact([], [], true));
      }

      return out;
    } catch (error) {
      env.newMessage(`failed to check ${toCheck}`);
      return RType.Error;
    }
  }

  function localEnvExec(env: L_Env, localEnvNode: LocalEnvNode): RType {
    try {
      const newEnv = new L_Env(env);
      for (let i = 0; i < localEnvNode.nodes.length; i++) {
        const out = nodeExec(newEnv, localEnvNode.nodes[i]);
        newEnv.getMessages().forEach((e) => env.newMessage(e));
        newEnv.clearMessages();
        if (RType.Error === out) return RType.Error;
      }

      return RType.True;
    } catch (error) {
      env.newMessage("{}");
      return RType.Error;
    }
  }

  function returnExec(env: L_Env, node: ReturnNode): RType {
    try {
      for (const f of node.facts) {
        if (env.someOptsDeclaredHere(f)) {
          env.newMessage(
            `Error: Some operators in ${f} are declared in block. It's illegal to declare operator or variable with the same name in the if-then expression you want to prove.`
          );
          return RType.Error;
        }
        if (env.someVarsDeclaredHere(f, [])) {
          env.newMessage(
            `Error: Some variables in ${f} are declared in block. It's illegal to declare operator or variable with the same name in the if-then expression you want to prove.`
          );
          return RType.Error;
        }
      }

      for (const toProve of node.facts) {
        const out = L_Checker.check(env, toProve);
        if (out !== RType.True) return out;
      }

      const storeTo = env.getFather();
      if (storeTo) {
        for (const toProve of node.facts) {
          L_FactStorage.store(storeTo, toProve, []);
        }
      }
      return RType.True;
    } catch (error) {
      env.newMessage("return");
      return RType.Error;
    }
  }

  function existExec(env: L_Env, node: ExistNode): RType {
    try {
      for (const fact of node.facts) {
        const out = L_Checker.check(env, fact);
        if (out !== RType.True) {
          env.newMessage(`Failed to check ${fact}`);
          return out;
        }
      }

      for (const fact of node.facts) {
        env.newHave(fact.fullName);
      }

      return RType.True;
    } catch (error) {
      env.newMessage("exist");
      return RType.Error;
    }
  }

  function returnExistExec(env: L_Env, node: ReturnExistNode): RType {
    try {
      for (const factName of node.factNames) {
        if (
          !(
            env.inHaves(factName) &&
            env.optDeclared(factName) &&
            !env.optDeclaredHere(factName)
          )
        ) {
          env.newMessage(
            `${factName} must be declared outside current environment and exist of this operator should be checked first.`
          );
          return RType.Error;
        }
      }

      let father = env.getFather();
      if (father) {
        for (const factName of node.factNames) {
          father.newHave(factName);
        }
      }

      return RType.True;
    } catch (error) {
      env.newMessage("return_exist");
      return RType.Error;
    }
  }

  function byExec(env: L_Env, byNode: ByNode): RType {
    try {
      const out = L_Checker.checkBy(env, byNode);
      if (out === RType.True) {
        let ok = L_FactStorage.storeFactInBy(env, byNode);
        if (!ok) {
          return RType.Error;
        }
      }

      return out;
    } catch (error) {
      env.newMessage("by");
      return RType.Error;
    }
  }
}
