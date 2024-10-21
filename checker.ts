import { FactNode, ShortCallOptNode } from "./ast";
import { L_Env, StoredFactValue } from "./env";
import { RType } from "./executor";

export namespace checker {
  function literallyCheckShortOpt(env: L_Env, opt: ShortCallOptNode): RType {
    const facts = env.shortOptFacts.get(opt.fullName);
    if (!facts) return RType.Error;

    for (const storedFact of facts) {
      if (storedFact.vars.every((ls, i) => ls.every((s, j) => checkSingleVar(s, opt.params[i][j])))) {
        if (storedFact.req.every(e => checker.check(env, e) == RType.True)) {
          env.messages.push(`${opt} is true, by ${storedFact}`)
          return RType.True
        }
      }
    }

    return RType.Unknown;

    function checkSingleVar(trueFact: string, toCheck: string) {
      return (trueFact.startsWith("#") || trueFact === toCheck);
    }
  }

  function checkOpt(env: L_Env, opt: ShortCallOptNode): RType {
    let out =  literallyCheckShortOpt(env, opt);
    if (!(out === RType.True)) return  out
    
    return out
  }

  export function check(env: L_Env, node: FactNode): RType {
    if (node instanceof ShortCallOptNode) {
      return checkOpt(env, node);
    }

    return RType.Error;
  }
}