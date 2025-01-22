import { L_Env } from "../L_Env";
import { OptFactNode } from "../L_Facts";
import { L_Out } from "../L_Structs";
import { L_Composite, L_Singleton, L_Symbol } from "../L_Symbols";

function isNaturalNumber(str: string) {
  const regex = /^(0|[1-9]\d*)$/;
  return regex.test(str);
}

export function addDefinition(env: L_Env, opt: OptFactNode): L_Out {
  if (opt.vars.length === 2 && opt.optSymbol.name === "=") {
    const left = addedSymbol(opt.vars[0]);
    const right = addedSymbol(opt.vars[1]);
    // undefined means the given symbol is not the required form
    if (left === undefined || right === undefined) return L_Out.Unknown;
    else {
      return left === right ? L_Out.True : L_Out.False;
    }
  }

  return L_Out.Unknown;

  function addedSymbol(symbol: L_Symbol): string | undefined {
    if (
      symbol instanceof L_Composite &&
      symbol.name === "+" &&
      symbol.values.length === 2 &&
      symbol.values.every(
        (e) => e instanceof L_Singleton && isNaturalNumber(e.value)
      )
    ) {
      return addStrings(
        (symbol.values[0] as L_Singleton).value,
        (symbol.values[1] as L_Singleton).value
      );
    } else if (symbol instanceof L_Singleton && isNaturalNumber(symbol.value)) {
      return symbol.value;
    }

    return undefined;
  }
}

function addStrings(num1: string, num2: string): string {
  let carry = "0";
  let result = [];
  let i = num1.length - 1;
  let j = num2.length - 1;

  const addSingleDigits = (
    d1: string,
    d2: string,
    carry: string
  ): [string, string] => {
    const digitMap = "0123456789";
    let sum =
      digitMap.indexOf(d1) + digitMap.indexOf(d2) + digitMap.indexOf(carry);
    const newCarry = digitMap[Math.floor(sum / 10)];
    const digit = digitMap[sum % 10];
    return [digit, newCarry];
  };

  while (i >= 0 || j >= 0 || carry !== "0") {
    const digit1 = i >= 0 ? num1[i] : "0";
    const digit2 = j >= 0 ? num2[j] : "0";

    const [sumDigit, newCarry] = addSingleDigits(digit1, digit2, carry);
    result.push(sumDigit);
    carry = newCarry;

    i--;
    j--;
  }

  return result.reverse().join("");
}

export function plusplusEqualsPlusOne(env: L_Env, opt: OptFactNode): L_Out {
  if (
    opt.optSymbol.name === "=" &&
    opt.vars.length === 2 &&
    opt.vars[0] instanceof L_Composite &&
    opt.vars[0].values[0] instanceof L_Singleton &&
    isNaturalNumber(opt.vars[0].values[0].value) &&
    opt.vars[1] instanceof L_Singleton &&
    isNaturalNumber(opt.vars[1].value) &&
    addStrings(opt.vars[0].values[0].value, "1") === opt.vars[1].value
  ) {
    return L_Out.True;
  }

  return L_Out.Unknown;
}
