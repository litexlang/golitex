import { ShortCallOptNode } from "./ast";
import { L_Env, StoredFactValue } from "./env";

class Checker {
  constructor() {

  }

  literallyCheckShortOpt(env: L_Env, opt: ShortCallOptNode): StoredFactValue[] {
    const facts = env.shortOptFacts.get(opt.fullName)
    if (!facts) return []
    
    const out: StoredFactValue[] = []
    for (const storedFact of facts) {
      if (storedFact.vars.every((ls,i) => ls.every((s,j) => checkSingleVar(s, opt.params[i][j])))) {
        out.push(storedFact)
      }
    }

    return out

    function checkSingleVar(trueFact:string, toCheck: string) {
      return (trueFact.startsWith("#") || trueFact === toCheck) 
    }
  }
}

const checker = new Checker();