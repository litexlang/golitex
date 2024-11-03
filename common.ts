export const specialChars = [
  "(",
  ")",
  "{",
  "}",
  "[",
  "]",
  ":",
  ",",
  ";",
  "\n",
  "!",
  "&",
  "|",
  "$",
];

export const KnowTypeKeywords = ["know", "assume"];
export const ThenKeywords = ["=>"];
export const OnlyIfThenKeywords = ["<="];
export const IffThenKeywords = ["<=>"];
export const IfKeywords = ["if"];
export const OnlyIfKeywords = ["only_if"];
export const IffKeywords = ["iff"];
export const ExistKeywords = ["exist"];
export const DefKeywords = ["def"];

export const SymbolsFactsSeparator = "|";
export const ProveKeywords = ["prove"];
// export const suchThats = ["st", "is"];

export const StdStmtEnds = [";", "\n"];
export const LetKeywords = ["let"];
export const HaveKeywords = ["have"];

export const ProveByContradictionKeyword = "prove_by_contradiction";
export const IsKeywords = ["is"];
export const AreKeywords = ["are"];
export const IsAreKeywords = [...IsKeywords, ...AreKeywords];
export const NotKeywords = ["not"];
export const OrKeywords = ["or"];
export const ByKeywords = ["by"];
export const WhenKeyword = "when";
export const ContradictionKeyword = "contradiction";

export const L_Keywords: string[] = [
  "#",
  WhenKeyword,
  ...specialChars,
  ...KnowTypeKeywords,
  ...ThenKeywords,
  ...OnlyIfThenKeywords,
  ...IffThenKeywords,
  ...IfKeywords,
  ...OnlyIfKeywords,
  ...IffKeywords,
  ...ExistKeywords,
  ...DefKeywords,
  ...ProveKeywords,
  ...StdStmtEnds,
  ...LetKeywords,
  ...HaveKeywords,
  ProveByContradictionKeyword,
  ...IsKeywords,
  ...AreKeywords,
  ...NotKeywords,
  ...OrKeywords,
  ...ByKeywords,
];

export const LogicalOptPairs: { [k: string]: string[] } = {
  if: ThenKeywords,
  iff: IffThenKeywords,
  only_if: OnlyIfThenKeywords,
};

export const LogicalKeywords = [
  ...IfKeywords,
  ...OnlyIfKeywords,
  ...IffKeywords,
];
