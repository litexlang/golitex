import { L_Env } from "../L_Env";
import { L_Composite, L_Singleton, L_Symbol } from "../L_Structs";

function isNaturalNumberStr(str: string) {
  const regex = /^(0|[1-9]\d*)$/;
  return regex.test(str);
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

export function arabic_plus(
  env: L_Env,
  composite: L_Composite
): L_Singleton | undefined {
  try {
    if (
      composite.name === "+" &&
      composite.values.length === 2 &&
      composite.values[0] instanceof L_Singleton &&
      composite.values[1] instanceof L_Singleton &&
      isNaturalNumberStr(composite.values[0].value) &&
      isNaturalNumberStr(composite.values[1].value)
    ) {
      return new L_Singleton(
        addStrings(composite.values[0].value, composite.values[1].value)
      );
    }

    return undefined;
  } catch {}
}
