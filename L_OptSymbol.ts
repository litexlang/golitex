import { L_KW } from "./L_Keywords";

export class OptSymbol {
  constructor(public name: string) {}

  toString() {
    return this.name;
  }

  fix(optMap: Map<string, string>) {
    const newName = optMap.get(this.name);
    if (newName !== undefined) return new OptSymbol(newName);
    else return this;
  }
}

export class FreeOptSymbol extends OptSymbol {}

export class EqualOptSymbol extends OptSymbol {
  constructor(name = L_KW.Equal) {
    super(name);
  }
}
export const EqualSymbol = new EqualOptSymbol();
