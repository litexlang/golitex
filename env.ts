export class LiTeXEnv {
  errors: string[] = [];
  constructor() {}

  pushErrorMessage(s: string) {
    this.errors.push(s);
  }
}
