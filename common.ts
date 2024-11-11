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

export const KnowTypeKeywords = [
  "know",
  "assume",
  "strict_know",
  "strict_assume",
];
export const ThenKeywords = ["=>"];
export const OnlyIfThenKeywords = ["<="];
export const IffThenKeywords = ["<=>"];
export const IfKeywords = ["if"];
export const OnlyIfKeywords = ["only_if"];
export const IffKeywords = ["iff"];
export const ExistKeyword = "exist";
export const DefKeywords = ["def"];

export const SymbolsFactsSeparator = ":";
export const ProveKeywords = ["prove"];
// export const suchThats = ["st", "is"];

export const StdStmtEnds = [";", "\n"];
export const LetKeywords = ["let", "strict_let"];
export const HaveKeywords = ["have"];
export const ByKeyword = "by";
export const ProveByContradictionKeyword = "prove_by_contradiction";
export const IsKeywords = ["is"];
export const AreKeywords = ["are"];
export const IsAreKeywords = [...IsKeywords, ...AreKeywords];
export const NotKeywords = ["not"];
export const OrKeywords = ["or"];
export const PostfixProveKeywords = ["prove"];
export const WhenKeyword = "when";
export const ContradictionKeyword = "contradiction";
export const ReturnKeyword = ["return", "so"];
export const ReturnExistKeyword = ["return_exist"];
export const DefByKeywords = ["def_by"];

export const NotsKeyword = "nots";
export const STKeyword = "st";

export const L_Keywords: string[] = [
  "#",
  ByKeyword,
  WhenKeyword,
  ...specialChars,
  ...KnowTypeKeywords,
  ...ThenKeywords,
  ...OnlyIfThenKeywords,
  ...IffThenKeywords,
  ...IfKeywords,
  ...OnlyIfKeywords,
  ...IffKeywords,
  ExistKeyword,
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
  ...PostfixProveKeywords,
  ...ReturnExistKeyword,
  ...ReturnKeyword,
  ...DefByKeywords,
  NotsKeyword,
  STKeyword,
];

export const LogicalOptPairs: { [k: string]: string[] } = {
  if: ThenKeywords,
  iff: IffThenKeywords,
  only_if: OnlyIfThenKeywords,
  exist: ThenKeywords,
};

export const LogicalKeywords = [...IfKeywords, ...IffKeywords];
