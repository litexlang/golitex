import {
  FactNode,
  IffNode,
  IfThenNode,
  KnowNode,
  L_Node,
  OnlyIfNode,
  OptNode,
} from "./ast";
import { L_Env, StoredFactValue } from "./L_Env";
import { L_Executor, RType } from "./L_Executor";
import { L_Saver } from "./L_Saver";

// export class CheckerOut {
//   constructor(
//     public type: RType,
//     public checkedByOpt: Boolean = false
//   ) {}
// }

// function checkAndMsg(env: L_Env, r: RType, n: L_Node): Boolean {
//   if (r === RType.Unknown) env.newMessage(`Unknown ${n}`);
//   if (r === RType.Error) env.newMessage(`Error ${n}`);
//   return r === RType.True;
// }

export namespace checker {
  // export function check(env: L_Env, node: FactNode): CheckerOut {
  //   if (node instanceof OptNode) {
  //     const out = checkOpt(env, node);
  //     return out;
  //   } else if (node instanceof IfThenNode) {
  //     const out = checkLogicalOpt(env, node.vars, node.req, node.onlyIfs);
  //     return new CheckerOut(out);
  //   } else if (node instanceof IffNode) {
  //     let out = checkLogicalOpt(env, node.vars, node.req, node.onlyIfs);
  //     if (!(out === RType.True)) return new CheckerOut(out);
  //     out = checkLogicalOpt(env, node.vars, node.onlyIfs, node.req);
  //     return new CheckerOut(out);
  //   } else if (node instanceof OnlyIfNode) {
  //     const out = checkLogicalOpt(env, node.vars, node.onlyIfs, node.req);
  //     return new CheckerOut(out);
  //   }

  //   return new CheckerOut(RType.Error);
  // }

  // /**
  //  * Main function of checker
  //  * @param env the environment we are working at
  //  * @param opt the fact (OptFact) we wanna prove
  //  * @param ignore  which fact (Opt) to ignore in order to avoid "req => itself, itself => req"-kind loop
  //  * @returns RType Error, True, False
  //  */
  // export function checkOpt(env: L_Env, opt: OptNode): CheckerOut {
  //   // get related fact from itself and its ancestors
  //   const facts: StoredFactValue[] | undefined = env.getOptFact(opt.fullName);
  //   if (facts === undefined) {
  //     if (env.getDeclFact(opt.fullName)) {
  //       return new CheckerOut(RType.Unknown);
  //     } else {
  //       env.newMessage(`${opt.fullName} not declared.`);
  //       return new CheckerOut(RType.Error);
  //     }
  //   }

  //   const varsNotDeclared = env.varsAreNotDeclared(opt.vars);
  //   if (varsNotDeclared) {
  //     env.newMessage(`Not all of ${opt.vars} are declared.`);
  //     return new CheckerOut(RType.Error);
  //   }

  //   for (const storedFact of facts) {
  //     /**
  //      * Main Logic of Checking Steps:
  //      * 1. literally correct and stored.isT === opt.isT
  //      * 2. req correct
  //      * 2.1 locally correct
  //      * 2.2 correctness is given by father
  //      */
  //     if (
  //       storedFact.isT === opt.isT &&
  //       storedFact.vars.every((s, j) => checkSingleVar(s, opt.vars[j]))
  //     ) {
  //       /**
  //        * check current opt by replacing potential hashed var with current var
  //        */
  //       //! I think the following fixing is buggy
  //       const freeToFixMap = new Map<string, string>();
  //       storedFact.vars.forEach((s, j) => freeToFixMap.set(s, opt.vars[j]));

  //       if (
  //         storedFact.req.every((e) => {
  //           let out: RType = RType.Error;
  //           if (e instanceof OptNode) {
  //             out = checkByFactsWithNoReq(env, fixFree(e, freeToFixMap));
  //           } else if (e instanceof IfThenNode) {
  //             out = checkLogicalOpt(env, e.vars, e.req, e.onlyIfs);
  //           }
  //           return out === RType.True;
  //         })
  //       ) {
  //         env.newMessage(`${opt} is true, by ${storedFact}`);
  //         if (storedFact.req.length === 0)
  //           return new CheckerOut(RType.True, true);
  //         else return new CheckerOut(RType.True);
  //       }
  //     }
  //   }
  //   return new CheckerOut(RType.Unknown);
  // }

  // /**
  //  * Steps
  //  * 1. open a new Env
  //  * 2. emit var and req defined in if-then to new env
  //  * 3. check onlyIfs of if-then
  //  */
  // export function checkLogicalOpt(
  //   env: L_Env,
  //   vars: string[],
  //   knowWhat: FactNode[],
  //   checkWhat: FactNode[]
  // ): RType {
  //   const newEnv = new L_Env(env);
  //   newEnv.declareNewVar(vars);
  //   L_Executor.knowExec(newEnv, new KnowNode(knowWhat));

  //   for (const fact of checkWhat) {
  //     const out = check(newEnv, fact);
  //     if (out.type === RType.Error) return RType.Error;
  //     else if ([RType.False, RType.Unknown].includes(out.type)) return out.type;
  //   }

  //   return RType.True;
  // }

  // export function checkByFactsWithNoReq(env: L_Env, node: FactNode): RType {
  //   if (node instanceof OptNode) {
  //     return checkOptByFactsWithNoReq(env, node);
  //   } else if (node instanceof IfThenNode) {
  //     return checkIfThenByFactsWithNoReq(env, node);
  //   }

  //   return RType.Error;
  // }

  // function checkOptByFactsWithNoReq(env: L_Env, opt: OptNode): RType {
  //   const facts = env.getOptFact(opt.fullName);
  //   if (!facts) return RType.Error;

  //   for (const storedFact of facts) {
  //     if (
  //       storedFact.isT === opt.isT &&
  //       storedFact.vars.every((s, j) => checkSingleVar(s, opt.vars[j])) &&
  //       storedFact.req.length === 0
  //     ) {
  //       return RType.True;
  //     }
  //   }

  //   return RType.Unknown;
  // }

  export function checkOptInHave(env: L_Env, opt: OptNode): RType {
    return RType.Unknown;
  }

  // function checkIfThenByFactsWithNoReq(env: L_Env, node: IfThenNode): RType {
  //   const newEnv = new L_Env(env);
  //   newEnv.declareNewVar(node.vars);
  //   L_Executor.knowExec(newEnv, new KnowNode(node.req));

  //   for (const fact of node.onlyIfs) {
  //     const out = checkByFactsWithNoReq(newEnv, fact);
  //     if (out === RType.Error) return RType.Error;
  //     else if ([RType.False, RType.Unknown].includes(out)) return out;
  //   }

  //   return RType.True;
  // }

  // function checkSingleVar(trueFact: string, toCheck: string): Boolean {
  //   return trueFact.startsWith("#") || trueFact === toCheck;
  // }

  // function fixFree(e: FactNode, freeToFixMap: Map<string, string>): FactNode {
  //   if (e instanceof IfThenNode) {
  //     return new IfThenNode(
  //       e.vars.map((s) => {
  //         const out = freeToFixMap.get(s);
  //         if (out === undefined) return s;
  //         else return out;
  //       }),
  //       [...e.req],
  //       [...e.onlyIfs]
  //     );
  //   } else if (e instanceof OptNode) {
  //     return new OptNode(
  //       e.fullName,
  //       e.vars.map((s) => {
  //         const out = freeToFixMap.get(s);
  //         if (out === undefined) return s;
  //         else return out;
  //       })
  //     );
  //   }
  //   throw Error("fact should be if-then or Opt");
  // }

  //==============================================================

  export function L_Check(env: L_Env, toCheck: FactNode): RType {
    if (toCheck instanceof OptNode) {
      return L_CheckOpt(env, toCheck);
    } else if (toCheck instanceof IfThenNode) {
      return L_CheckIfThen(env, toCheck);
    }

    return RType.Unknown;
  }

  export function L_CheckOpt(env: L_Env, toCheck: OptNode): RType {
    const storedFacts: L_Saver.StoredFact[] | undefined =
      env.getStoredFactsFromAllLevels(toCheck.fullName);
    if (storedFacts === undefined) return RType.Unknown;

    for (const storedFact of storedFacts) {
      if (toCheck.vars.length !== storedFact.vars.length) {
        env.newMessage(
          `Invalid number of arguments: need ${storedFact.vars.length}, get ${toCheck.vars.length}`
        );
        return RType.Error;
      }

      let unknown = false;
      if (storedFact.isNoReq()) {
        if (L_CheckOptLiterally(env, toCheck)) {
          return RType.True;
        } else {
          continue;
        }
      }

      const map = new Map<String, string>();
      for (let i = 0; i < toCheck.vars.length; i++) {
        // check whether a variable is already declared at current level, for example, `if x,x | ...` is not allowed
        if (map.get(storedFact.vars[i])) {
          env.newMessage(`Double declaration of ${storedFact.vars[i]}`);
          return RType.Error;
        }

        map.set(storedFact.vars[i], toCheck.vars[i]);
      }

      // try to use the current storedFact ot prove toCheck

      const frees = storedFact.getAllFreeVars();

      // satisfy all requirements

      let newEnv = new L_Env(env);

      for (const currentLevelReq of storedFact.req) {
        // try to operate(store facts, introduce new variables) under current layer of stored if-then
        currentLevelReq.vars.forEach((e) =>
          newEnv.newFreeFix(e, map.get(e) as string)
        );

        // satisfy literal restrictions
        for (const req of currentLevelReq.req) {
          if (req instanceof OptNode) {
            const checkReq = new OptNode(
              req.fullName,
              req.vars.map((e) => newEnv.getVar(e)) as string[]
            );
            const out = L_CheckOptLiterally(newEnv, checkReq);
            if (out) continue;
            else {
              unknown = true;
              break;
            }
          } else if (req instanceof IfThenNode) {
            const out = L_CheckOpt(newEnv, toCheck); //! toCheck here is wrong
            if (out === RType.True) continue;
            else if (out === RType.Unknown || out === RType.Error) {
              unknown = true;
              break;
            }
          }
        }

        if (unknown) break;
        else newEnv = new L_Env(newEnv);
      }
      if (unknown) continue;
      return RType.True;
    }

    return RType.Unknown;
  }

  // check whether a variable in fact.vars is free or fixed at check time instead of run time.
  export function L_CheckOptLiterally(env: L_Env, toCheck: OptNode): Boolean {
    const facts: L_Saver.StoredFact[] | undefined =
      env.getStoredFactsFromAllLevels(toCheck.fullName);

    if (facts === undefined) return false;

    for (const fact of facts) {
      const frees = fact.getAllFreeVars();
      if (
        fact.isNoReq() &&
        toCheck.vars.every(
          (v, i) => frees.includes(fact.vars[i]) || v === fact.vars[i]
        )
      )
        return true;
    }

    return false;
  }

  export function L_CheckIfThen(env: L_Env, toCheck: IfThenNode): RType {
    let out: RType = RType.True;
    const newEnv = new L_Env(env);
    toCheck.vars.forEach((e) => newEnv.newVar(e, e));
    L_Executor.knowExec(newEnv, new KnowNode(toCheck.req));
    for (const onlyIf of toCheck.onlyIfs) {
      out = L_Check(newEnv, onlyIf);
      if (out !== RType.True) return out;
    }
    return RType.True;
  }
}
