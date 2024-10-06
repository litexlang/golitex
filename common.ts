export const specialChars = [
  "(",
  ")",
  "{",
  "}",
  ":",
  ",",
  ";",
  "@",
  "!",
  "$",
  "?",
  "&",
];

export const OptsConnectionSymbol = ":";
export const KnowTypeKeywords = [
  "@",
  "know",
  "suppose",
  "know_everything",
  "!",
];
export const ExistKeywords = ["exist", "?"];
export const TemplateDeclarationKeywords = [":", "def", ...ExistKeywords];

export const DefBlockDeclareAndCall = "$"; // sort of works like do in coffeeScript and (function (...){...}).call(...) in JS

export const SeparationBetweenSymbolsAndTheirFacts = ":";
export const ProveKeywords = ["&", "prove"];
