import { L_Env } from "../L_Env";
import { OptNode } from "../L_Nodes";
import { L_Composite, L_Out, L_Singleton } from "../L_Structs";

export function addDefinition(env: L_Env, opt: OptNode): L_Out {
  if (opt.vars.length === 2) {
    if (
      opt.optSymbol.name === "=" &&
      opt.vars[0] instanceof L_Singleton &&
      opt.vars[1] instanceof L_Composite
    ) {
      if (
        opt.vars[1].name === "+" &&
        opt.vars[1].values.length === 2 &&
        opt.vars[1].values.every((e) => e instanceof L_Singleton)
      ) {
        if (
          opt.vars[0].value ===
          addStrings(opt.vars[1].values[0].value, opt.vars[1].values[1].value)
        ) {
          return L_Out.True;
        }
      }
    }
  }

  return L_Out.Unknown;

  function addStrings(num1: string, num2: string) {
    let carry = 0; // 进位
    let result = [];
    let i = num1.length - 1;
    let j = num2.length - 1;

    while (i >= 0 || j >= 0 || carry > 0) {
      const digit1 = i >= 0 ? num1.charCodeAt(i) - "0".charCodeAt(0) : 0;
      const digit2 = j >= 0 ? num2.charCodeAt(j) - "0".charCodeAt(0) : 0;

      const sum = digit1 + digit2 + carry;
      result.push(sum % 10); // 当前位
      carry = Math.floor(sum / 10); // 进位
      i--;
      j--;
    }

    return result.reverse().join("");
  }
}
