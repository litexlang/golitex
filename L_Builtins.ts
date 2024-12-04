import { L_Node, OptNode, ToCheckNode } from "./L_Nodes";
import { L_Env } from "./L_Env";
import { nodeExec } from "./L_Executor";
import { checkOptLiterally } from "./L_Checker";
import { reportNewExist } from "./L_Messages";
import { KnownExist, L_Out } from "./L_Structs";

export const L_BuiltinsKeywords: string[] = [
  "is_property",
  // "exist",
  "or",
  "is_composite",
];

export function isToCheckBuiltin(node: ToCheckNode): boolean {
  return node instanceof OptNode && L_BuiltinsKeywords.includes(node.name);
}

// Separate functions from the map
export function isPropertyBuiltinCheck(env: L_Env, node: OptNode): L_Out {
  try {
    const out = env.getDef(node.vars[0]);
    if (out === undefined) {
      env.newMessage(
        `is_property error: ${node.name} is an undeclared operator.`
      );
      return L_Out.Error;
    } else {
      if (out.vars.length !== Number(node.vars[1])) {
        env.newMessage(
          `is_property error: ${node.name} requires ${
            out.vars.length
          } parameters, ${Number(node.vars[1])} given.`
        );
        return L_Out.Error;
      } else {
        return L_Out.True;
      }
    }
  } catch {
    return L_Out.Error;
  }
}

// export function existBuiltinCheck(env: L_Env, node: OptNode): L_Out {
//   try {
//     return L_Out.True;
// for (let i = 0; i < node.vars.length; i++) {
//   if (env.isExisted(node.vars[i]) === node.isT) {
//     return L_Out.True;
//   }
//   const toCheck = new OptNode(
//     node.vars[i],
//     (node.checkVars as string[][])[i]
//   );
//   // Strict checking for existence
//   if (!L_BuiltinsKeywords.includes(node.vars[i])) {
//     const out = checkOptLiterally(env, toCheck);
//     if (out === L_Out.True) {
//       env.newExist(node.vars[i], new KnownExist(node.isT));
//     } else {
//       return out;
//     }
//   } else {
//     return env.errMesReturnL_Out(
//       `exist operator should not take builtin keyword ${node.vars[i]} as parameter.`
//     );
//   }
// }
// return L_Out.True;
//   } catch {
//     return L_Out.Error;
//   }
// }

export function isCompositeBuiltinCheck(env: L_Env, node: OptNode): L_Out {
  try {
    if (node.vars.length !== 1) {
      return L_Out.Error;
    } else {
      if (node.vars[0].startsWith("\\")) {
        return L_Out.True;
      }
    }

    return L_Out.True;
  } catch {
    return L_Out.Error;
  }
}

export function orBuiltinCheck(env: L_Env, node: OptNode): L_Out {
  try {
    return L_Out.True;
  } catch {
    return L_Out.Error;
  }
}
