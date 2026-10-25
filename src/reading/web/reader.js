/* The same component is used by local preview, static export and host websites. */
(function (global) {
  "use strict";
  const copy = {
    en: { source:"Source", why:"Why it holds", verified:"Verified", failed:"Incomplete verification", accepted:"Accepted", rejected:"Not established", premise:"Actual grounds", rules:"Rules used", concepts:"Concepts", proof:"Explore the evidence", raw:"Inspect reading data", empty:"Follow the mathematics", emptyHint:"Open a .lit file or a complete Litex project to explore its statements, definitions and proof grounds.", definition:"Definition", references:"Occurrences", rulebook:"Rule Book", search:"Search rules", usedOnly:"Used in this book", noPremise:"This record has no earlier stored-fact citation.", unavailable:"Some reading information has not been exported.", catalogueOnly:"Catalogue identity; an authored description is not available in this bundle.", previous:"Previous", next:"Next",  back:"Back", selectedLegend:"Selected statement", premiseLegend:"Cited fact", noRules:"This statement does not use a builtin rule.", sourceLine:"Source line", noDefinition:"No source declaration is recorded in this bundle.", local:"Local proof context", engine:"Built with", uses:"Used here", notFalse:"A failed check does not prove the statement false." },
    zh: { source:"源码", why:"这句话为什么成立", verified:"验证通过", failed:"验证未全部通过", accepted:"已接受", rejected:"尚未建立", premise:"实际采用的依据", rules:"本次使用的规则", concepts:"概念", proof:"展开证明依据", raw:"查看阅读数据", empty:"沿着依据，读懂数学", emptyHint:"打开 .lit 文件或完整 Litex 项目，探索陈述、定义和证明依据之间的联系。", definition:"定义", references:"出现位置", rulebook:"规则手册", search:"搜索规则", usedOnly:"只看本书使用的规则", noPremise:"本条记录没有引用更早的已存事实。", unavailable:"部分阅读信息尚未导出。", catalogueOnly:"本条目记录了规则身份；数据包尚未提供完整说明。", previous:"上一页", next:"下一页",  back:"返回", selectedLegend:"当前陈述", premiseLegend:"引用的事实", noRules:"本句没有使用内置规则。", sourceLine:"源码行", noDefinition:"数据包中没有记录对应的源码声明。", local:"局部证明上下文", engine:"构建内核", uses:"在这里使用", notFalse:"检查未通过，并不表示这句话为假。" }
  };
  Object.assign(copy.en,{title:"Interactive textbook",hint:"Select source to read its explanation; follow facts or concepts to explore further.",therefore:"Therefore",previousStep:"Previous",nextStep:"Next",occurrenceLegend:"Concept",notExported:"Execution evidence unavailable",outerProof:"Enclosing proof",context:"Context",sourceMappingGap:"Some nested execution results have no precise source mapping.",category:"Rule category",allCategories:"All categories",builtin:"Builtin rules",builtin_theorem:"Builtin theorems",infer:"Inference rules",user_trust:"User assumption",axiom:"Axiom",axiom_release:"Axiom application"});
  Object.assign(copy.zh,{title:"可交互教科书",hint:"点击源码查看说明，点击事实或概念继续探索。",therefore:"因此",previousStep:"上一步",nextStep:"下一步",occurrenceLegend:"概念",notExported:"执行依据未导出",outerProof:"上一层证明",context:"Context",sourceMappingGap:"部分内部执行结果尚无精确的源码映射。",category:"规则分类",allCategories:"全部分类",builtin:"内置规则",builtin_theorem:"内置定理",infer:"推导规则",user_trust:"用户假设",axiom:"公理",axiom_release:"公理应用"});
  Object.assign(copy.en,{declarations:"Definitions and theorems used",trust:"Assumptions and axioms",trustUsed:"This derivation depends on these explicit assumptions or axioms."});
  Object.assign(copy.zh,{declarations:"采用的定义与定理",trust:"假设与公理",trustUsed:"这条推导依赖以下显式假设或公理。"});
  Object.assign(copy.en,{inferred:"Inferred fact",inferredFacts:"Facts inferred here",inferredFrom:"Inferred from",producer:"Source statement"});
  Object.assign(copy.zh,{inferred:"推导事实",inferredFacts:"本句推导出的事实",inferredFrom:"由此推导",producer:"产生它的原语句"});
  Object.assign(copy.en,{inferredCount:"Inferred {count}",closeInferences:"Close inferred facts"});
  Object.assign(copy.zh,{inferredCount:"推导 {count}",closeInferences:"收起推导结果"});
  Object.assign(copy.en,{inferenceBasis:"Inference basis",fromNamedDefinition:"From definition {name}",fromDefinition:"From the definition",fromNamedParamType:"From {name}'s parameter types",fromParamType:"From parameter types",fromRule:"By rule {name}",originUnavailable:"Inference origin unavailable",batchRules:"Rules used in this inference batch"});
  Object.assign(copy.zh,{inferenceBasis:"推导依据",fromNamedDefinition:"由定义 {name} 展开",fromDefinition:"由定义展开",fromNamedParamType:"由 {name} 的参数类型推出",fromParamType:"由参数类型推出",fromRule:"由规则 {name} 推出",originUnavailable:"推导来源尚未细分",batchRules:"本批推导使用的规则"});
  Object.assign(copy.en,{parameterTypeRecord:"Parameter type record",definitionResult:"Definition expansion",parameterTypeHint:"This records the argument's type, as specified by the definition.",definitionResultHint:"Unfolding the definition gives this fact.",inferenceSources:"Source statements",sourceStatement:"Original statement",inferenceSeed:"Facts involved",parameterTypesRule:"Parameter types",definitionExpansionRule:"Unfold a definition"});
  Object.assign(copy.zh,{parameterTypeRecord:"参数类型记录",definitionResult:"定义展开结果",parameterTypeHint:"这条记录表示本次参数的类型，类型要求来自所用定义。",definitionResultHint:"展开所用定义后，得到这条事实。",inferenceSources:"查看来源",sourceStatement:"原语句",inferenceSeed:"涉及的事实",parameterTypesRule:"参数类型",definitionExpansionRule:"展开定义"});
  Object.assign(copy.en,{fact:"Fact",hypothesis:"Local hypothesis",declaration:"Introduced by a declaration",verifiedFact:"Established fact",formation:"Formation evidence",hypothesisHint:"This fact is assumed inside the enclosing proof context.",declarationHint:"This fact is introduced by the object or parameter declaration.",factSourceGap:"This bundle has no source producer for this fact.",factProofGap:"Fact-specific evidence is unavailable; inspect its source statement."});
  Object.assign(copy.zh,{fact:"事实",hypothesis:"局部假设",declaration:"由声明引入",verifiedFact:"已建立的事实",formation:"表达式有定义的依据",hypothesisHint:"这条事实是所在证明上下文中的假设。",declarationHint:"这条事实由对象或参数的声明引入。",factSourceGap:"数据包尚未记录这条事实的来源语句。",factProofGap:"本条事实的独立依据尚未导出，可查看来源语句。"});
  Object.assign(copy.en,{wellDefined:"Well-defined expression",registration:"Registration",registrationHint:"The engine recorded this exact expression as well-defined in this scope.",registrationProof:"Its formation evidence is retained by the source statement.",wdGap:"Some well-definedness registrations have no exported source."});
  Object.assign(copy.zh,{wellDefined:"表达式有定义",registration:"登记记录",registrationHint:"内核在此作用域中登记了这个表达式有定义。",registrationProof:"其形成依据保留在来源语句中。",wdGap:"部分有定义登记尚未关联到导出的来源。"});
  Object.assign(copy.en,{book:"Contents and search",chapters:"Chapters",dependencies:"Dependencies",bookSearch:"Search all source",loading:"Loading chapter…",loadingIndex:"Loading search index…",noMatches:"No matches",sourceText:"Source text",noStatement:"This source line has no exported execution statement.",changedBuild:"The reading data changed. Reopen the book.",loadFailed:"Could not load reading data"});
  Object.assign(copy.zh,{book:"目录与搜索",chapters:"章节",dependencies:"依赖模块",bookSearch:"搜索全书源码",loading:"正在加载章节…",loadingIndex:"正在加载搜索索引…",noMatches:"没有匹配结果",sourceText:"源码文本",noStatement:"这行源码没有对应的执行语句记录。",changedBuild:"阅读数据已更新，请重新打开这本书。",loadFailed:"无法加载阅读数据"});
  Object.assign(copy.en,{statementDetails:"Statement details",statementType:"Statement type",typeUnavailable:"This bundle does not include the statement type.",statementFactHint:"A fact assertion and its recorded verification grounds.",statementDefinitionHint:"Defines a name, interface or mathematical structure.",statementDeclarationHint:"Introduces objects and records the facts established by this declaration.",statementProofHint:"A proof step with its target and recorded grounds.",statementReleaseHint:"Unpacks an existing theorem or definition into usable facts.",statementRegistrationHint:"Registers a property for subsequent uses of this predicate.",statementTrustHint:"Introduces an explicit assumption or axiom.",statementCommandHint:"Runs a session command.",propDefinitionHint:"Defines the predicate's parameters and the conditions under which it holds.",abstractDefinitionHint:"Declares a predicate's name and parameter interface.",theoremDefinitionHint:"States a named theorem with its proof.",introducedFacts:"Facts introduced here",validationBasis:"Facts used to check this statement",referencedDefinitions:"Definitions referenced"});
  Object.assign(copy.zh,{statementDetails:"语句详情",statementType:"语句类型",typeUnavailable:"此数据包尚未提供语句类型。",statementFactHint:"陈述一条事实，并查看实际记录的验证依据。",statementDefinitionHint:"定义名称、接口或数学结构。",statementDeclarationHint:"引入对象，并记录这次声明建立的事实。",statementProofHint:"展示这一步证明的目标和实际采用的依据。",statementReleaseHint:"展开已有定理或定义，取得可用的事实。",statementRegistrationHint:"登记命题的性质，供后续使用。",statementTrustHint:"引入显式假设或公理。",statementCommandHint:"执行会话命令。",propDefinitionHint:"定义这个命题的参数和成立条件。",abstractDefinitionHint:"声明命题的名称与参数接口。",theoremDefinitionHint:"给出命名定理及其证明。",introducedFacts:"本句引入的事实",validationBasis:"检查本句时采用的事实",referencedDefinitions:"引用的定义"});
  Object.assign(copy.en,{mathematicalMeaning:"Mathematical meaning",parameterRange:"Parameter domain",iff:"if and only if",and:"and",setKind:"is a set",nonemptySetKind:"is a nonempty set",finiteSetKind:"is a finite set",takeObjects:"Choose objects in the following domains",alsoSatisfies:"Also satisfying",valueRange:"Value range",meaningUnavailable:"A mathematical explanation is not available in this bundle yet.",abstractMeaning:"This predicate is specified by its interface; no equivalent conditions are defined here.",closeHelp:"Close explanation",typeHelp:"About this statement type",inferredHelp:"A recorded consequence of processing a statement, available for later citations.",mathGrounds:"Grounds",underHypotheses:"Under the current proof assumptions",unverifiedMeaning:"This statement has not been established.",unexecutedMeaning:"This statement has not been executed in this context.",viewDefinition:"Definition: {name}",viewSource:"Locate in source"});
  Object.assign(copy.zh,{mathematicalMeaning:"数学含义",parameterRange:"参数范围",iff:"当且仅当",and:"且",setKind:"是集合",nonemptySetKind:"是非空集合",finiteSetKind:"是有限集合",takeObjects:"在以下范围内取对象",alsoSatisfies:"同时满足",valueRange:"取值范围",meaningUnavailable:"此数据包暂未提供这条语句的数学解释。",abstractMeaning:"这是由接口指定的命题，此处没有定义它的等价条件。",closeHelp:"收起说明",typeHelp:"这种语句的作用",inferredHelp:"这是处理语句时记录的推导结果，可以被后续语句引用。",mathGrounds:"依据",underHypotheses:"在当前证明假设下",unverifiedMeaning:"这条语句尚未建立。",unexecutedMeaning:"这条语句在此上下文中尚未执行。",viewDefinition:"定义：{name}",viewSource:"在源码中定位"});
  Object.assign(copy.en,{propGuideTitle:"What is a prop statement?",propGuidePurpose:"prop gives a name to a mathematical condition with parameters. You can then use that name in theorem statements and proofs.",propGuideUse:"A definition does not establish any particular instance. An instance holds when its arguments satisfy all the defining conditions.",propGuideExample:"An example",propGuideMeaning:"Here x R requires a real argument, and nonnegative(x) means that x is nonnegative. The definition does not assert that every real number is nonnegative.",propGuideProof:"by def $nonnegative(3) substitutes 3 for x and checks 3 >= 0. This establishes the fact that 3 is nonnegative, which later statements can use."});
  Object.assign(copy.zh,{propGuideTitle:"什么是 prop 语句？",propGuidePurpose:"prop 用来给一个带参数的数学条件起名字，定义一个命题。这样就能在定理和证明中反复使用这个名字。",propGuideUse:"定义本身不证明任何具体实例。代入的参数满足定义中的全部条件时，对应的命题才成立。",propGuideExample:"一个例子",propGuideMeaning:"这里 x R 要求参数是实数，nonnegative(x) 表示“x 非负”。这个定义没有声称所有实数都非负。",propGuideProof:"by def $nonnegative(3) 把 x 换成 3，检查 3 >= 0，建立“3 非负”这个事实，后面的语句就可以继续使用它。"});
  Object.assign(copy.en,{typesettingUnavailable:"Formula typesetting is unavailable; showing the retained mathematical text.",propHelpButton:"About prop"});
  Object.assign(copy.zh,{typesettingUnavailable:"公式排版暂不可用，以下保留完整的数学文本。",propHelpButton:"了解 prop 语句"});
  Object.assign(copy.en,{referenceCount:"{count} references",currentFileReferences:"Current file · {count} references",noReferences:"No source references in this file.",referenceHelp:"Source references only; excludes the declaration and inferred output.",closeReferences:"Close references",referenceFor:"References to {name}",referenceLine:"Line {line}"});
  Object.assign(copy.zh,{referenceCount:"引用 {count} 处",currentFileReferences:"当前文件 · {count} 处",noReferences:"当前文件没有源码引用。",referenceHelp:"只统计源码中的引用，不含定义本身和推导输出。",closeReferences:"收起引用",referenceFor:"{name} 的引用",referenceLine:"第 {line} 行"});
  // Keys are exported AST variants, not keywords inferred from source text.
  const statementTypes = {
    Fact:["Fact assertion","事实陈述","fact"],
    Definition:["Definition statement","定义语句"],Trust:["Explicit assumption","显式假设"],By:["Proof step","证明步骤"],ReleaseAndExpand:["Unpacking statement","展开语句"],Register:["Property registration","性质登记"],Witness:["Witness proof","构造见证"],ProofBlock:["Proof block","证明块"],Command:["Session command","会话命令"],
    DefPropStmt:["Proposition definition","命题定义","prop","propDefinitionHint"],DefAbstractPropStmt:["Abstract proposition declaration","抽象命题声明","abstract_prop","abstractDefinitionHint"],DefThmStmt:["Theorem","定理","thm","theoremDefinitionHint"],AxiomStmt:["Axiom declaration","公理声明","axiom"],DefStrategyStmt:["Proof strategy definition","证明策略定义","strategy"],DefTemplateStmt:["Template definition","模板定义","template"],DefStructStmt:["Structure definition","结构定义","struct"],
    LetObjStmt:["Object binding","对象绑定","let"],HaveObjInNonemptySetStmt:["Object declaration","对象声明","have"],HaveObjEqualStmt:["Object definition by equality","等式定义对象","have"],HaveObjByExistFactsStmt:["Objects from existence","由存在性引入对象","have"],ObtainObjFromExistFact:["Witness extraction","提取存在见证","obtain"],ObtainObjFromAtomicFact:["Witness extraction from a predicate","从命题提取见证","obtain"],HaveByPreimageStmt:["Preimage object declaration","引入原像对象","have by fn_preimage"],HaveByReplacementAxiomStmt:["Replacement construction","替换公理构造","have by replacement_axiom"],
    HaveFnEqualStmt:["Function definition","函数定义","have fn"],HaveFnEqualCaseByCaseStmt:["Function definition by cases","分情况定义函数","have fn"],HaveFnByInducStmt:["Function definition by induction","归纳定义函数","have fn"],HaveFnByForallExistUniqueStmt:["Function from unique existence","由唯一存在性定义函数","have fn"],DefAlgoByCasesStmt:["Algorithm by cases","分情况定义算法","algo"],DefAlgoByInducStmt:["Algorithm by induction","归纳定义算法","algo"],
    ByDefStmt:["Definition expansion","按定义展开","by def"],ByThmStmt:["Theorem application","应用定理","by thm"],ByCasesStmt:["Proof by cases","分类证明","by cases"],ByContraStmt:["Proof by contradiction","反证法","by contra"],ByEnumerateFiniteSetStmt:["Proof by finite enumeration","有限枚举证明","by enumerate"],ByInducStmt:["Induction proof","归纳证明","by induc"],ByStrongInducStmt:["Strong induction proof","强归纳证明","by strong_induc"],ByForStmt:["Range enumeration proof","范围枚举证明","by for"],ByExtensionStmt:["Set extensionality proof","集合外延证明","by extension"],ByFnExtensionStmt:["Function extensionality proof","函数外延证明","by fn_extension"],
    ReleaseThmStmt:["Theorem instantiation","实例化定理","release thm"],ReleaseStructDefStmt:["Structure definition release","展开结构定义","release"],ReleaseObjDefStmt:["Object definition release","展开对象定义","release"],ReleaseCartDefStmt:["Cartesian product definition release","展开笛卡尔积定义","release"],ReleaseTupleDefStmt:["Tuple definition release","展开元组定义","release"],ExpandRangeStmt:["Range membership expansion","展开范围归属","expand"],ReleaseZornLemmaStmt:["Zorn's lemma application","应用佐恩引理","release"],ReleaseAxiomOfChoiceStmt:["Axiom of choice application","应用选择公理","release"],ReleaseRegularityAxiomStmt:["Regularity axiom application","应用正则公理","release"],
    RegisterTransitivePropStmt:["Transitivity registration","登记传递性","register transitive"],RegisterSymmetricPropStmt:["Symmetry registration","登记对称性","register symmetric"],RegisterReflexivePropStmt:["Reflexivity registration","登记自反性","register reflexive"],WitnessExistFact:["Existence proof by witness","构造存在见证","witness"],WitnessAtomicFact:["Predicate proof by witness","构造命题见证","witness"],WitnessNonemptySet:["Nonemptiness proof by witness","构造非空集合见证","witness"],ClaimStmt:["Local claim","局部断言","claim"],SketchStmt:["Proof sketch","证明草稿","sketch"],TrustStmt:["Explicit assumption","显式假设","trust"],TrustHaveStmt:["Objects with explicit assumptions","带假设的对象声明","trust have"],EvalStmt:["Expression evaluation","表达式求值","eval"]
  };
  const roles = { base_in_real_proof:["Real base", "底数属于实数"], nonnegative_addend_proof:["Nonnegative addend", "加项非负"], well_defined_proof:["Well-defined expressions", "表达式有定义"], well_defined:["Well-defined expressions", "表达式有定义"], searched_proof:["Selected proof", "采用的证明"], verify_result:["Verification grounds", "验证依据"], store_and_infer_result:["Established knowledge", "建立的知识"], store_and_infer:["Established knowledge", "建立的知识"], local_env:["Local context", "局部上下文"], introduced_params:["Introduced parameters", "引入的参数"], assumed_dom_facts:["Local hypotheses", "局部假设"], proved_then_facts:["Conclusions", "结论"], cite_fact_id:["Cited fact", "引用的事实"], source_fact_id:["Source fact", "来源事实"], fact:["Statement", "数学陈述"], statement:["Source statement", "源码陈述"], value:["Evidence", "依据"] };
  const routeNames = { ByKnownAtomicFact:["Earlier fact", "更早的事实"], ByKnownForallFact:["Earlier universal fact", "更早的全称事实"], ByEquivalenceClass:["Stored equalities", "已建立的等式"], ByLocalIntroduction:["Local proof", "局部证明"], ByBuiltinRule:["Builtin rule", "内置规则"], ByBuiltinStrategy:["Structured derivation", "结构化推导"], ByBuiltinRewrite:["Checked rewrite", "经过检查的改写"], Success:["Established", "已建立"], Failed:["Not established", "尚未建立"] };
  function element(tag, className, content) { const node=document.createElement(tag); if(className)node.className=className; if(content!==undefined)node.textContent=String(content); return node; }
  function button(label, className, callback) { const node=element("button",className,label); node.type="button"; node.addEventListener("click",callback); return node; }
  function array(value) { return Array.isArray(value)?value:[]; }
  function humanize(value) { return String(value||"").replace(/([a-z])([A-Z])/g,"$1 $2").replace(/_/g," "); }
  function bytePositions(source) { const positions=new Map([[0,0]]); let bytes=0,units=0; for(const char of source){ const point=char.codePointAt(0); bytes+=point<128?1:point<2048?2:point<65536?3:4; units+=char.length; positions.set(bytes,units); } return positions; }

  Object.assign(copy.zh,{readingHelp:"阅读帮助",advancedHelp:"深入查看",records:"阅读记录",openFiles:"打开文件",openProject:"打开文件夹",recordExplanation:"阅读记录里保存了每句话怎样被检查、用到了哪些已知事实、又推出了什么。网页根据这些记录展示原文和说明。",recordFileExplanation:"这些记录保存成 JSON 文件，换一台电脑也能打开查看。JSON 是这种文件格式的名字。",book:"示例目录",hint:"点一句，看看它的意思；点灰色结果，看看推出了什么。"});
  Object.assign(copy.en,{readingHelp:"Reading help",advancedHelp:"Explore further",records:"Reading records",openFiles:"Open a file",openProject:"Open a folder",recordExplanation:"Reading records save how each statement was checked, which known facts it used, and what it led to. This page uses those records to show the source and its explanations.",recordFileExplanation:"Records are saved as a JSON file, which you can open on another computer. JSON is the name of the file format.",book:"Examples",hint:"Click a statement to see its meaning. Click a grey result to explore what follows."});

  // Authored language help. Token boundaries come from the real tokenizer;
  // builtin-set meanings are keyed by resolved identities, never source names.
  const syntaxHelp={
    prop:["定义命题：给出它的参数和成立条件。","Define a predicate with parameters and defining conditions."],
    abstract_prop:["声明抽象命题接口，不给出等价定义。","Declare a predicate interface without a defining equivalence."],
    have:["引入对象或函数，并检查声明要求。","Introduce an object or function and check its declaration requirements."],
    let:["引入当前上下文中的变量或绑定。","Introduce a variable or binding in the current context."],
    fn:["函数：描述参数和取值类型。","Function: describe parameter and result types."],
    forall:["全称量词 ∀：对指定范围内的每一个对象。","Universal quantifier ∀: for every object in the specified domain."],
    exist:["存在量词 ∃：存在满足条件的对象。","Existential quantifier ∃: an object satisfying the conditions exists."],
    "exist!":["唯一存在 ∃!：恰有一个对象满足条件。","Unique existence ∃!: exactly one object satisfies the conditions."],
    claim:["提出待证明的结论，并在块内给出证明。","State a goal and provide its proof in the block."],
    thm:["定义可供后文使用的定理。","Define a theorem for later use."],
    by:["指定证明或展开所采用的方法。","Specify a proof or expansion method."],
    def:["按定义检查或展开命题。","Check or unfold a predicate by its definition."],
    contra:["反证法：假设结论不成立并推出矛盾。","Proof by contradiction: negate the goal and derive a contradiction."],
    cases:["分情况证明。","Prove by cases."],
    case:["一个分支的条件与证明。","A case condition and its proof."],
    induc:["归纳证明。","Proof by induction."],
    strong_induc:["强归纳证明。","Proof by strong induction."],
    obtain:["从已知存在事实中取出见证对象。","Obtain witness objects from an existence fact."],
    witness:["提供满足存在性结论的具体见证。","Supply a concrete witness for an existence goal."],
    trust:["显式信任：此处内容作为假设接受。","Explicit trust: accept the content here as an assumption."],
    axiom:["声明公理，作为后续推理的前提。","Declare an axiom as a premise for subsequent reasoning."],
    struct:["定义带字段与约束的结构。","Define a structure with fields and constraints."],
    template:["定义可实例化的模板。","Define a template that can be instantiated."],
    set:["集合参数类型。","Set parameter type."],
    nonempty_set:["非空集合参数类型。","Nonempty-set parameter type."],
    finite_set:["有限集合参数类型。","Finite-set parameter type."],
    in:["属于 ∈：左边的对象属于右边的集合。","Membership ∈: the object on the left belongs to the set on the right."],
    and:["且 ∧：各条件同时成立。","Conjunction ∧: all conditions hold."],
    or:["或 ∨：至少一个条件成立。","Disjunction ∨: at least one condition holds."],
    not:["否定 ¬：后面的命题不成立。","Negation ¬: the following proposition does not hold."],
    "=>":["蕴含 ⇒：前面的条件推出后面的结论。","Implication ⇒: the preceding conditions imply the conclusion."],
    "<=>":["等价 ⇔：两边互相推出。","Equivalence ⇔: each side implies the other."],
    "?":["标出待证明的目标。","Mark a goal to be proved."],
    "$" :["命题应用的前缀。","Prefix for a predicate application."],
    "=":["相等。","Equality."],
    "!=":["不相等 ≠。","Inequality ≠."],
    "<=":["小于或等于 ≤。","Less than or equal to ≤."],
    ">=":["大于或等于 ≥。","Greater than or equal to ≥."],
    "<":["小于。","Less than."],
    ">":["大于。","Greater than."]
  };
  // Phrases are language help over adjacent lexer spans, not parsed mathematics.
  const syntaxPhrases={
    "by def":["用定义来证明。","Prove using a definition."],
    "by contra":["用反证法证明：假设结论不成立，再推出矛盾。","Prove by contradiction: negate the goal and derive a contradiction."],
    "by cases":["分情况证明，每一种情况都要成立。","Prove each case."],
    "by induc":["用数学归纳法证明。","Prove by mathematical induction."],
    "by strong_induc":["用强归纳法证明。","Prove by strong induction."],
    "by thm":["用已有定理证明。","Prove using a theorem."],
    "have fn":["定义函数，给出参数和函数值。","Define a function with its parameters and value."],
    "release thm":["使用已有定理，得到它给出的结论。","Apply a theorem and make its conclusions available."]
  };
  // BEGIN GENERATED LEXICAL KINDS
  const lexicalKinds=new Map([["keyword",["?","abstract_prop","algo","and","as","axiom","axiom_of_choice","by","case","cases","claim","contra","def","enumerate","eval","exist","exist!","expand","extension","fn","fn_extension","for","forall","from","have","import","impossible","induc","let","not","obtain","or","prop","reflexive","register","regularity_axiom","release","replacement_axiom","sketch","st","strategy","strong_induc","struct","symmetric","template","thm","transitive","trust","witness","zorn_lemma"]],["predicate",["$","bijective","coprime","dvd","fn_eq","fn_eq_in","has_derivative_at","has_limit_at","has_limit_left","has_limit_neg_inf","has_limit_pos_inf","has_limit_right","has_riemann_integral","has_seq_liminf","has_seq_limit","has_seq_limsup","in","injective","is_cart","is_choice_function_for","is_continuous","is_continuous_at","is_continuous_left","is_continuous_right","is_differentiable_at","is_finite_set","is_lipschitz","is_nonempty_set","is_real_accumulation_at","is_real_accumulation_left","is_real_accumulation_right","is_real_bounded","is_real_bounded_above","is_real_bounded_below","is_real_lower_bound","is_real_upper_bound","is_riemann_integrable","is_seq_bounded","is_seq_bounded_above","is_seq_bounded_below","is_seq_cauchy","is_seq_convergent","is_seq_nondecreasing","is_seq_nonincreasing","is_seq_strictly_decreasing","is_seq_strictly_increasing","is_set","is_tuple","is_uniformly_continuous","prime","proper_subset","proper_superset","subset","superset","surjective","∉"]],["function",["C_abs","abs","arccos","arccot","arcsin","arctan","cart","cart_dim","cart_n","ceil","closed_range","compose","conj","conjugate_transpose","cos","cosh","cot","coth","csc","csch","derivative","det","exp","factorial","family_intersect","family_union","finite_seq","finite_set_max","finite_set_min","finite_set_product","finite_set_reduce","finite_set_size","finite_set_sum","floor","fn_preimage","fn_range","gcd","identity_matrix","img","index_cart","index_intersect","index_union","inf","integral","intersect","lcm","lim","lim_left","lim_neg_inf","lim_pos_inf","lim_right","liminf","limsup","ln","log","max","min","power_set","preimage","preimage_set","product","proj","quot","range","re","reduce","sec","sech","seq","set_diff","set_minus","sign","sin","sinh","sqrt","sum","sup","tan","tanh","trace","transpose","tuple","tuple_dim","union","zero_matrix"]],["type",["C","C*","N","N+","Q","Q*","Q+","Q-","R","R*","R+","R-","Z","Z*","Z+","Z-","finite_set","matrix","nonempty_set","obj","set","ℂ*","ℕ+","ℚ*","ℚ+","ℚ-","ℝ*","ℝ+","ℝ-","ℤ*","ℤ+","ℤ-"]],["constant",["e","i","pi"]],["operator",["!","!=","%","&","'*","'+","'-","'^","*","*'","+","-","->","/","<","<=","<=>","=","=>",">",">=","^","×","∘","∩","∪"]],["punctuation",["'","(",")",",",".","...",":","::",":::","[","\\","]","{","|","}"]]].flatMap(([kind,tokens])=>tokens.map(token=>[token,kind])));
  // END GENERATED LEXICAL KINDS
  const syntaxRoleHelp={
    keyword:["Litex 关键词。","Litex keyword."],
    predicate:["谓词：表达一个数学条件。","Predicate: express a mathematical condition."],
    function:["函数：把参数映射到一个值。","Function: map arguments to a value."],
    object:["对象","Object"],
    type:["类型或集合：描述对象的范围。","Type or set: describe a domain of objects."],
    theorem:["已命名的定理、公理或证明策略。","Named theorem, axiom or proof strategy."]
  };
  const standardSetHelp={
    N:["自然数集 ℕ（含 0）","Natural numbers ℕ (including 0)"],
    Z:["整数集 ℤ","Integers ℤ"], Q:["有理数集 ℚ","Rational numbers ℚ"],
    R:["实数集 ℝ","Real numbers ℝ"], C:["复数集 ℂ","Complex numbers ℂ"],
    "N+":["正自然数集","Positive natural numbers"],
    "Z+":["正整数集","Positive integers"], "Q+":["正有理数集","Positive rational numbers"], "R+":["正实数集","Positive real numbers"],
    "Z-":["负整数集","Negative integers"], "Q-":["负有理数集","Negative rational numbers"], "R-":["负实数集","Negative real numbers"],
    "Z*":["非零整数集","Nonzero integers"], "Q*":["非零有理数集","Nonzero rational numbers"], "R*":["非零实数集","Nonzero real numbers"], "C*":["非零复数集","Nonzero complex numbers"]
  };

  // Authored language-reference hints, not inferred expression types.
  // Domains follow verify_obj/scalar.rs and ast/obj.rs. Resolved user symbols
  // retain their own declaration help; token spelling never overrides identity.
  const builtinObjectHelp={
  "+": [
    "a + b",
    "a, b ∈ ℂ → ℂ",
    "加法。自然数、整数、有理数、实数也可以相加。",
    "Addition; also accepts natural, integer, rational and real operands.",
    "1 + 2 = 3"
  ],
  "-": [
    "a - b; -a",
    "a, b ∈ ℂ → ℂ",
    "减法；放在一个数前表示取相反数。结果未必仍是自然数。",
    "Subtraction; unary minus takes the additive inverse. The result need not be natural.",
    "2 - 5 = -3"
  ],
  "*": [
    "a * b",
    "a, b ∈ ℂ → ℂ",
    "乘法。",
    "Multiplication.",
    "3 * 4 = 12"
  ],
  "/": [
    "a / b",
    "a, b ∈ ℂ; b ≠ 0 → ℂ",
    "除法。除数必须不为零，结果不一定是整数。",
    "Division. The divisor must be nonzero; the result need not be an integer.",
    "3 / 2 = 1.5"
  ],
  "^": [
    "a ^ b",
    "(a ∈ ℂ, b ∈ ℕ) ∪ (a ∈ ℂ\\{0}, b ∈ ℤ)\n∪ (a > 0, a,b ∈ ℝ) ∪ (a ≥ 0, b > 0, a,b ∈ ℝ) → ℂ",
    "乘方。Litex 中 0^0 = 1；不支持一般的复数指数或负底数的非整数指数。",
    "Exponentiation. Litex sets 0^0 = 1; general complex exponents and noninteger powers of negative bases are unsupported.",
    "2 ^ 3 = 8"
  ],
  "%": [
    "a % b",
    "a, b ∈ ℤ; b ≠ 0 → ℕ",
    "欧几里得余数，满足 0 ≤ r < |b|。",
    "Euclidean remainder r, with 0 ≤ r < |b|.",
    "7 % 3 = 1"
  ],
  "sqrt": [
    "sqrt(x)",
    "x ∈ ℝ; x ≥ 0 → ℝ≥0",
    "非负平方根：结果的平方等于 x，且结果不小于零。",
    "The nonnegative square root: its square is x.",
    "sqrt(4) = 2"
  ],
  "abs": [
    "abs(x)",
    "x ∈ ℝ → ℝ≥0",
    "实数的绝对值，即它到零的距离。复数的模使用 C_abs。",
    "Real absolute value, the distance to zero. Use C_abs for complex modulus.",
    "abs(-3) = 3"
  ],
  "min": [
    "min(a, b)",
    "a, b ∈ ℝ → ℝ",
    "取两个实数中较小的一个。",
    "The smaller of two real numbers.",
    "min(2, 5) = 2"
  ],
  "max": [
    "max(a, b)",
    "a, b ∈ ℝ → ℝ",
    "取两个实数中较大的一个。",
    "The larger of two real numbers.",
    "max(2, 5) = 5"
  ],
  "floor": [
    "floor(x)",
    "x ∈ ℝ → ℤ",
    "向下取整：不大于 x 的最大整数。",
    "The greatest integer at most x.",
    "floor(2.5) = 2"
  ],
  "ceil": [
    "ceil(x)",
    "x ∈ ℝ → ℤ",
    "向上取整：不小于 x 的最小整数。",
    "The least integer at least x.",
    "ceil(2.5) = 3"
  ],
  "sign": [
    "sign(x)",
    "x ∈ ℝ → {-1, 0, 1}",
    "负数取 -1，零取 0，正数取 1。",
    "Returns -1 for negative x, 0 for zero, and 1 for positive x.",
    "sign(-3) = -1"
  ],
  "exp": [
    "exp(x)",
    "x ∈ ℝ → ℝ>0",
    "以自然常数 e 为底的指数函数 e^x。",
    "The real exponential e^x.",
    "exp(0) = 1"
  ],
  "ln": [
    "ln(x)",
    "x ∈ ℝ; x > 0 → ℝ",
    "自然对数，以 e 为底。",
    "The natural logarithm, with base e.",
    "ln(1) = 0"
  ],
  "log": [
    "log(b, x)",
    "b, x ∈ ℝ; b > 0, b ≠ 1, x > 0 → ℝ",
    "以 b 为底、x 的对数；第一个参数是底数。",
    "The logarithm of x to base b; the base is the first argument.",
    "log(2, 8) = 3"
  ],
  "factorial": [
    "factorial(n)",
    "n ∈ ℕ → ℕ>0",
    "阶乘：从 1 乘到 n，约定 0! = 1；也可写 n!。",
    "Factorial: the product from 1 to n, with 0! = 1. Also written n!.",
    "factorial(3) = 6"
  ],
  "gcd": [
    "gcd(a, b)",
    "a, b ∈ ℤ; (a ≠ 0 ∨ b ≠ 0) → ℕ>0",
    "最大公约数，取正值；不接受两个参数都为零。",
    "The positive greatest common divisor; the all-zero pair is excluded.",
    "gcd(12, 18) = 6"
  ],
  "lcm": [
    "lcm(a, b)",
    "a, b ∈ ℤ → ℕ",
    "最小非负公倍数；任一参数为零时结果为零。",
    "The least nonnegative common multiple, zero when either argument is zero.",
    "lcm(4, 6) = 12"
  ],
  "quot": [
    "quot(a, d)",
    "a ∈ ℤ, d ∈ ℕ>0 → ℤ",
    "欧几里得整商，满足 a = d * quot(a,d) + a % d。",
    "Euclidean integer quotient: a = d * quot(a,d) + a % d.",
    "quot(7, 3) = 2"
  ],
  "sin": [
    "sin(x)",
    "x ∈ ℝ → [-1, 1]",
    "正弦函数，角度使用弧度。",
    "Sine, with angles in radians.",
    "sin(0) = 0"
  ],
  "cos": [
    "cos(x)",
    "x ∈ ℝ → [-1, 1]",
    "余弦函数，角度使用弧度。",
    "Cosine, with angles in radians.",
    "cos(0) = 1"
  ],
  "tan": [
    "tan(x)",
    "x ∈ ℝ; cos(x) ≠ 0 → ℝ",
    "正切函数 sin(x)/cos(x)，角度使用弧度。",
    "Tangent sin(x)/cos(x), with angles in radians.",
    "tan(0) = 0"
  ],
  "cot": [
    "cot(x)",
    "x ∈ ℝ; sin(x) ≠ 0 → ℝ",
    "余切函数 cos(x)/sin(x)，角度使用弧度。",
    "Cotangent cos(x)/sin(x), with angles in radians.",
    "cot(pi / 4) = 1"
  ],
  "arcsin": [
    "arcsin(x)",
    "x ∈ [-1, 1] → [-π/2, π/2]",
    "反正弦，结果是主值区间中的弧度。",
    "Principal inverse sine, returned in radians.",
    "arcsin(0) = 0"
  ],
  "arccos": [
    "arccos(x)",
    "x ∈ [-1, 1] → [0, π]",
    "反余弦，结果是主值区间中的弧度。",
    "Principal inverse cosine, returned in radians.",
    "arccos(1) = 0"
  ],
  "arctan": [
    "arctan(x)",
    "x ∈ ℝ → (-π/2, π/2)",
    "反正切，结果是主值区间中的弧度。",
    "Principal inverse tangent, returned in radians.",
    "arctan(0) = 0"
  ],
  "re": [
    "re(z)",
    "z ∈ ℂ → ℝ",
    "复数的实部。",
    "The real part of a complex number.",
    "re(i) = 0"
  ],
  "img": [
    "img(z)",
    "z ∈ ℂ → ℝ",
    "复数的虚部，结果是实数。",
    "The imaginary part of a complex number, returned as a real number.",
    "img(i) = 1"
  ],
  "conj": [
    "conj(z)",
    "z ∈ ℂ → ℂ",
    "复共轭：a + b*i 变成 a - b*i。",
    "Complex conjugate: a + b*i becomes a - b*i.",
    "conj(i) = -i"
  ],
  "C_abs": [
    "C_abs(z)",
    "z ∈ ℂ → ℝ≥0",
    "复数的模，即复平面上到原点的距离。",
    "Complex modulus, the distance to the origin in the complex plane.",
    "C_abs(i) = 1"
  ]
};

  // Authored reference cards describe builtin contracts, not the inferred type
  // of a hovered expression. Set-kind inputs are never a universal set domain.
  const setOperatorHelp={
    union:["union(A, B)","A、B 是集合；结果是集合 A ∪ B。","A and B are sets; the result is the set A ∪ B.","并集：包含属于 A 或属于 B 的元素。","Union: elements belonging to A or B.","1 $in union({1}, {2})"],
    intersect:["intersect(A, B)","A、B 是集合；结果是集合 A ∩ B。","A and B are sets; the result is the set A ∩ B.","交集：只包含同时属于 A 和 B 的元素。","Intersection: elements belonging to both A and B.","2 $in intersect({1, 2}, {2, 3})"],
    set_minus:["set_minus(A, B)","A、B 是集合；结果是 A 的子集。","A and B are sets; the result is a subset of A.","差集：包含属于 A 但不属于 B 的元素。","Relative complement: elements in A but not in B.","1 $in set_minus({1, 2}, {2})"],
    power_set:["power_set(A)","A 是集合；结果是由 A 的所有子集组成的集合。","A is a set; the result is the set of all subsets of A.","幂集：它的每个元素都是 A 的一个子集。","Power set: each of its elements is a subset of A.","power_set({1}) = {{}, {1}}"],
    family_union:["family_union(F)","F 是集合族（每个元素都是集合）；结果是集合。","F is a set of sets; the result is a set.","集合族的并：包含至少属于 F 中一个集合的元素。","Union of a family: elements in at least one member of F.","family_union({{1, 2}}) = {1, 2}"],
    family_intersect:["family_intersect(F)","F 是非空集合族（每个元素都是集合）；结果是集合。","F is a nonempty set of sets; the result is a set.","集合族的交：包含属于 F 中每一个集合的元素。","Intersection of a family: elements in every member of F.","$is_set(family_intersect({{1}}))"],
    index_union:["index_union(I, X, A)","I 是非空集合，X 是集合；A ∈ fn(k I) power_set(X)；结果是 X 的子集。","I is a nonempty set and X is a set; A ∈ fn(k I) power_set(X); the result is a subset of X.","指标并集：把每个 k ∈ I 对应的集合 A(k) 合并。","Indexed union: combine A(k) for every k ∈ I.","let U = index_union({1}, N, fn(k {1}) power_set(N) {{2}})"],
    index_intersect:["index_intersect(I, X, A)","I 是非空集合，X 是集合；A ∈ fn(k I) power_set(X)；结果是 X 的子集。","I is a nonempty set and X is a set; A ∈ fn(k I) power_set(X); the result is a subset of X.","指标交集：取 X 中属于每个 A(k) 的元素；Litex 要求 I 非空。","Indexed intersection: elements of X in every A(k); Litex requires nonempty I.","let J = index_intersect({1}, N, fn(k {1}) power_set(N) {{2}})"]
  };
  // Alternate builtin spellings share documentation only, never public APIs.
  setOperatorHelp.set_diff=setOperatorHelp.set_minus;
  setOperatorHelp["∪"]=setOperatorHelp.union;setOperatorHelp["∩"]=setOperatorHelp.intersect;
  Object.assign(builtinObjectHelp,{
    arccot:["arccot(x)","x ∈ ℝ → (0, π)","反余切，取 (0, π) 中的主值，单位为弧度。","Principal inverse cotangent in (0, π), in radians.","arccot(0) = pi / 2"],
    sec:["sec(x)","x ∈ ℝ; cos(x) ≠ 0 → ℝ","正割，等于 1 / cos(x)。","Secant, equal to 1 / cos(x).","sec(0) = 1"],
    csc:["csc(x)","x ∈ ℝ; sin(x) ≠ 0 → ℝ","余割，等于 1 / sin(x)。","Cosecant, equal to 1 / sin(x).","csc(pi / 2) = 1"],
    sinh:["sinh(x)","x ∈ ℝ → ℝ","双曲正弦，等于 (exp(x) - exp(-x)) / 2。","Hyperbolic sine: (exp(x) - exp(-x)) / 2.","sinh(0) = 0"],
    cosh:["cosh(x)","x ∈ ℝ → [1, ∞)","双曲余弦，等于 (exp(x) + exp(-x)) / 2。","Hyperbolic cosine: (exp(x) + exp(-x)) / 2.","cosh(0) = 1"],
    tanh:["tanh(x)","x ∈ ℝ → (-1, 1)","双曲正切，等于 sinh(x) / cosh(x)。","Hyperbolic tangent: sinh(x) / cosh(x).","tanh(0) = 0"],
    coth:["coth(x)","x ∈ ℝ; x ≠ 0 → ℝ","双曲余切，等于 cosh(x) / sinh(x)；零处无定义。","Hyperbolic cotangent: cosh(x) / sinh(x); undefined at zero.","coth(1) = cosh(1) / sinh(1)"],
    sech:["sech(x)","x ∈ ℝ → (0, 1]","双曲正割，等于 1 / cosh(x)。","Hyperbolic secant: 1 / cosh(x).","sech(0) = 1"],
    csch:["csch(x)","x ∈ ℝ; x ≠ 0 → ℝ","双曲余割，等于 1 / sinh(x)；零处无定义。","Hyperbolic cosecant: 1 / sinh(x); undefined at zero.","csch(1) = 1 / sinh(1)"]
  });
  const keywordReference={
    prop:{
      syntax:"prop name(x A):\n    condition",
      zh:["谓词定义","定义带类型参数的谓词。","对声明域内的参数，谓词成立等价于定义体中的全部条件同时成立。定义本身不证明任何具体实例。"],
      en:["Predicate definition","Define a predicate with typed parameters.","For arguments in the declared domains, the predicate holds exactly when all conditions in its definition hold. The definition proves no particular instance."],
      example:"prop nonnegative(x R):\n    x >= 0\n\nby def $nonnegative(3)",
      walkthrough:{
        zh:[
          ["参数类型","x 是形式参数，R 将它的取值范围限定为实数集。实例中的实参必须属于该集合。"],
          ["谓词","nonnegative(x) 是关于实数 x 的命题，表示 x 非负；它不是返回一个数值的函数。"],
          ["定义条件","本例的定义体只有 x >= 0 一个条件。因此，对每个实数 x，有以下等价关系；若定义体有多个条件，则要求它们同时成立。","\\forall x\\in\\mathbb{R},\\quad \\operatorname{nonnegative}(x)\\iff x\\ge 0","∀ x ∈ ℝ: nonnegative(x) ⇔ x ≥ 0"],
          ["定义与实例","这条定义没有断言所有实数都非负，也没有证明某个具体实数非负。例如，nonnegative(-2) 不成立，因为 -2 < 0。"],
          ["按定义证明","最后一行 by def $nonnegative(3) 将实参 3 代入 x。验证 3 ∈ ℝ 和 3 ≥ 0 后，建立事实 $nonnegative(3)，后续证明可以引用这一事实。"]
        ],
        en:[
          ["Typed parameter","x is a formal parameter whose domain R is the set of real numbers. An actual argument must belong to this set."],
          ["Predicate","nonnegative(x) is a proposition about a real number x: x is nonnegative. It is not a function returning a numerical value."],
          ["Defining condition","The definition has one condition, x >= 0. Thus the following equivalence holds for every real x. With several defining conditions, all must hold.","\\forall x\\in\\mathbb{R},\\quad \\operatorname{nonnegative}(x)\\iff x\\ge 0","∀ x ∈ ℝ: nonnegative(x) ⇔ x ≥ 0"],
          ["Definition and instance","This declaration neither asserts that every real number is nonnegative nor proves a particular real number nonnegative. For example, nonnegative(-2) does not hold because -2 < 0."],
          ["Proof by definition","The last line, by def $nonnegative(3), substitutes the actual argument 3 for x. Verifying 3 ∈ ℝ and 3 ≥ 0 establishes $nonnegative(3), which later proofs may cite."]
        ]
      }
    },
    "by def":{
      syntax:"by def $name(arguments)",
      zh:["按定义证明","按谓词定义证明一个实例。","将实参代入定义，在参数类型要求满足的前提下证明全部定义条件；成功后得到对应的谓词事实。"],
      en:["Proof by definition","Prove an instance using its predicate definition.","Substitute the actual arguments, establish their declared types and prove every defining condition. Success establishes the corresponding predicate fact."],
      example:"prop nonnegative(x R):\n    x >= 0\n\nby def $nonnegative(3)",
      walkthrough:{
        zh:[
          ["代入实参","nonnegative 的形式参数是 x，本次实参是 3。代入后，定义体的 x >= 0 成为 3 >= 0。"],
          ["验证类型与条件","声明要求 x ∈ ℝ，因此先验证 3 ∈ ℝ；随后验证唯一的定义条件 3 ≥ 0。若定义有多个条件，每个条件都需要成立。"],
          ["得到实例事实","这些要求均得到验证后，by def 建立 $nonnegative(3)，供后续证明引用。它证明的是这个实例，不是所有实数都非负。"]
        ],
        en:[
          ["Substitute the argument","The formal parameter of nonnegative is x; the actual argument is 3. Substitution turns the defining condition x >= 0 into 3 >= 0."],
          ["Verify the type and condition","The declaration requires x ∈ ℝ, so verify 3 ∈ ℝ and then the single defining condition 3 ≥ 0. If the definition contains several conditions, every condition must hold."],
          ["Establish the instance","Once these requirements are established, by def establishes $nonnegative(3) for later citation. It proves this instance, not that every real number is nonnegative."]
        ]
      }
    },
    forall:{syntax:"forall x A:\n    condition",zh:["全称量词 ∀","说明指定集合中的每一个对象都满足某个条件。","在块内 x 是任意一个 A 中的对象。证明不能依赖 x 的某个特殊取值；x 的这个绑定只在本量词范围内有效。"],en:["Universal quantifier ∀","State a condition for every object in a given set.","Inside the block, x is an arbitrary member of A, not a chosen special value. Its binding is scoped to this quantifier."],example:"forall x R:\n    x = x"},
    claim:{syntax:"claim:\n    ? goal\n    proof",zh:["声明并证明","把要证明的目标和它的证明放在同一个块里。","? 标出目标。块内可以补充中间步骤；只有目标被证明后，承诺的结论才交给后文使用。"],en:["State and prove","Place a goal and its proof in one block.","? marks the goal. Intermediate steps can be added inside; the promised conclusion becomes available after it is established."],example:"claim:\n    ? 1 = 1\n    1 = 1"},
    "have fn":{syntax:"have fn f(x A) B = expression",zh:["定义函数","给出参数的范围，以及每个参数对应的函数值。","输入 x 属于 A；表达式的值必须属于 B。以后可以用 f(x) 引用这个值。"],en:["Function definition","Specify an input domain and the value assigned to each argument.","Input x belongs to A and the expression must belong to B. Later expressions may refer to this value as f(x)."],example:"have fn double(x R) R = 2 * x"},
    "by contra":{syntax:"by contra:\n    ? goal\n    proof",zh:["反证法","假设目标不成立，再推出矛盾，从而证明目标。","否定目标得到的假设只供当前证明使用。必须真正推出矛盾，不能只重复目标。"],en:["Proof by contradiction","Assume the negation of the goal and derive a contradiction.","The negated goal is local to this proof. A contradiction must be established, rather than merely repeating the goal."],example:"by contra:\n    ? not 1 = 2\n    impossible 1 = 2"}
  };

  function mountReadingReader(root, options) {
    options=options||{};
    let bundle=options.document||{sources:[],statements:[],rules:[]};
    let loader=options.loader||null,generation=0,navigationSerial=0;
    let operationStatus="",operationError=false;
    let bookQuery="",bookOpen=null,bookIndex=null,bookSerial=0,bookPage=0,bookSearch,bookResults,bookStatus;
    let allOccurrencesLoaded=!loader;
    let locale=options.locale||bundle.language||"en";
    let state={source:null,statement:null,symbol:null,fact:null,wd:null,focusLine:null};
    let history=[];
    let sources,statements,statementsBySource,facts,symbols,rules,occurrences,usedRules,evidenceNodes,inferences,wellDefinedness;
    let codePane,detailPane,rulebook,ruleGrid,ruleSearch,usedOnly,paging;
    let referencesBySource,declarationsBySource,symbolRoles,symbolDefinitions,symbolBindings,symbolParameters,displayNames;
    let rulePage=0,activeRule=null;
    let rulebookState={query:"",usedOnly:true,open:false,category:"all"};
    let destroyed=false,tokenHelp=null,inferencePopover=null;
    const drafts=new Map(),originals=new Map(),idePositions=new Map(),tokenHelpOpeners=new WeakMap();
    let restoreIdeFocus=false;
    let revision=0,checkedRevision=0,checking=false,editError="";
    const editText=(zh,en)=>lang()==="zh"?zh:en;
    function pending(){return revision!==checkedRevision;}
    function draftContent(source){return drafts.get(source.path)??source.content??"";}
    async function checkDraft(){
      if(checking||!options.onCheck)return;
      const epoch=generation,submitted=revision,path=sources.get(state.source)?.path,cursor=idePositions.get(sources.get(state.source)?.path)?.start;checking=true;editError="";
      const control=root.querySelector(".lr-check");if(control)control.disabled=true;
      detailPane.replaceChildren(element("p","lr-loading",editText("正在检查…","Checking…")));
      try{
        const result=await options.onCheck({changes:Object.fromEntries(drafts),sourcePath:path,locale:lang()});
        if(destroyed||epoch!==generation||submitted!==revision)return;
        api.update(result,{preserveDrafts:true});checkedRevision=submitted;
        const selected=[...sources.values()].find(source=>source.path===path);
        if(selected){
          const line=String(selected.content||"").slice(0,cursor??0).split("\n").length,entries=statementsBySource.get(selected.id)||[];
          const target=entries.find(value=>value.status==="rejected")||entries.filter(value=>value.line<=line).sort((a,b)=>b.line-a.line)[0]||initialStatement(selected.id);
          state.source=selected.id;state.statement=target?.id||null;state.focusLine=target?.line||line;
        }
      }catch(error){if(!destroyed&&epoch===generation&&submitted===revision)editError=error.message;}
      finally{checking=false;if(!destroyed)render();}
    }
    function renderEditor(source,sourcePane,header){
      if(!originals.has(source.path))originals.set(source.path,source.content||"");
      const check=button(editText("检查","Check"),"lr-button lr-check",checkDraft);check.disabled=checking;
      const restore=button(editText("恢复原文","Restore original"),"lr-button",()=>{drafts.set(source.path,originals.get(source.path));revision++;editError="";render();});
      header.append(check,restore);
      const editor=element("div","lr-ide"),canvas=element("div","lr-ide-canvas"),input=element("textarea","lr-editor-input lr-ide-input");
      input.dataset.sourcePath=source.path;input.value=draftContent(source);input.spellcheck=false;input.wrap="off";input.setAttribute("aria-label",editText("Litex 编辑器","Litex editor"));input.setAttribute("autocapitalize","off");input.setAttribute("autocomplete","off");input.setAttribute("autocorrect","off");
      codePane.classList.add("lr-ide-code");codePane.scrollTop=0;codePane.scrollLeft=0;
      canvas.append(codePane,input);editor.append(canvas);sourcePane.append(editor,element("div","lr-editor-hint",editText("直接输入 · ⌘ / Ctrl + Enter 检查 · 悬浮查看定义","Type here · ⌘ / Ctrl + Enter to check · Hover for definitions")));
      const drawDraft=()=>{
        codePane.replaceChildren();
        // Unchecked text receives lexical colors only, never old symbol identities.
        for(const [i,line] of input.value.split("\n").entries()){
          const row=element("div","lr-code-row"),number=element("span","lr-line-number",String(i+1)),code=element("code","lr-source-code");
          row.dataset.line=String(i+1);
          for(const token of line.match(/#[^\n]*|\b[0-9]+(?:\.[0-9]+)?\b|[A-Za-z_][A-Za-z_0-9]*|[^A-Za-z_0-9#]+|./g)||[]){
            const role=token.startsWith("#")?"comment":lexicalKinds.get(token)||(/^\d/.test(token)?"number":"identifier");code.append(element("span","lr-syntax-"+role,token));
          }
          if(!line)code.append(document.createTextNode(" "));row.append(number,code);codePane.append(row);
        }
      };
      const remember=()=>idePositions.set(source.path,{start:input.selectionStart,end:input.selectionEnd,top:editor.scrollTop,left:editor.scrollLeft});
      editor.addEventListener("scroll",remember);input.addEventListener("select",remember);
      const changed=()=>{drafts.set(source.path,input.value);revision++;editError="";hideTokenHelp();drawDraft();remember();invalidateEvidence();};
      input.addEventListener("input",changed);
      // The input owns typing; semantic hover resolves against the real checked
      // tokens underneath it, using their existing help callbacks and FactIds.
      const underneath=event=>{
        input.style.pointerEvents="none";const target=document.elementFromPoint(event.clientX,event.clientY);input.style.pointerEvents="";
        return target&&codePane.contains(target)?target:null;
      };
      input.addEventListener("pointermove",event=>{
        if(pending()||source.editor_unchecked){hideTokenHelp();return;}
        const token=underneath(event)?.closest(".lr-token,[data-syntax]");
        const show=token&&tokenHelpOpeners.get(token);if(show)show();else hideTokenHelp();
      });
      input.addEventListener("pointerleave",hideTokenHelp);
      input.addEventListener("pointerdown",event=>{
        if(pending())return;
        const target=underneath(event),action=target?.closest(".lr-inference-toggle,.lr-reference-count");
        const token=target?.closest(".lr-token,[data-keyword]");
        if(action||((event.ctrlKey||event.metaKey)&&token)){event.preventDefault();event.stopPropagation();remember();(action||token).click();}
      });
      const inspectCaret=(keyword=null)=>{
        remember();if(pending()||source.editor_unchecked)return;
        const before=input.value.slice(0,input.selectionStart),line=before.split("\n").length,start=before.lastIndexOf("\n")+1;
        const owner=owningStatement(source.id,line,new TextEncoder().encode(input.value.slice(0,start)).length);
        if(state.statement===owner?.id&&state.focusLine===line&&!state.fact&&!state.symbol&&(state.keyword||null)===keyword)return;
        closeInferences();state={source:source.id,statement:owner?.id||null,focusLine:line,symbol:null,fact:null,wd:null,keyword};
        const cited=new Set(array(owner?.cited_fact_ids)),premiseLines=new Set([...cited].map(id=>factLocation(facts.get(id))).filter(value=>value.sourceId===source.id).map(value=>value.line));
        for(const row of codePane.querySelectorAll(".lr-code-row")){const number=Number(row.dataset.line);row.classList.toggle("lr-selected",number===line);row.classList.toggle("lr-premise",number!==line&&premiseLines.has(number));}
        for(const toggle of codePane.querySelectorAll(".lr-inference-toggle")){toggle.classList.remove("lr-inferred-selected");toggle.classList.toggle("lr-inferred-premise",JSON.parse(toggle.dataset.facts).some(id=>cited.has(id)));}
        codePane.querySelectorAll(".lr-symbol-selected,.lr-reference-selected").forEach(node=>node.classList.remove("lr-symbol-selected","lr-reference-selected"));
        root.querySelector(".lr-inspector-title").textContent=keyword?editText("参考说明","Reference"):t("mathematicalMeaning");const presentation=statementPresentation(owner);root.querySelector(".lr-type-label").textContent=keyword||presentation.syntax||presentation.title;
        detailPane.replaceChildren();renderInspectorContents();
        if(options.onNavigate)options.onNavigate({...state},{bundle_id:bundle.bundle_id||null});
      };
      input.addEventListener("click",event=>{if(!underneath(event)?.closest(".lr-inference-toggle,.lr-reference-count"))inspectCaret(underneath(event)?.closest("[data-keyword]")?.dataset.keyword||null);});input.addEventListener("keyup",event=>{if(["ArrowUp","ArrowDown","ArrowLeft","ArrowRight","Home","End"].includes(event.key))inspectCaret();});
      input.addEventListener("keydown",event=>{
        if(event.isComposing)return;
        if(event.key==="Escape"){hideTokenHelp();return;}
        if((event.metaKey||event.ctrlKey)&&event.key==="Enter"){event.preventDefault();remember();checkDraft();}
        else if(event.key==="Tab"){event.preventDefault();input.setRangeText("    ",input.selectionStart,input.selectionEnd,"end");changed();}
        else if(event.key==="Enter"){
          const before=input.value.slice(0,input.selectionStart),line=before.slice(before.lastIndexOf("\n")+1),indent=line.match(/^ */)[0]+(line.trimEnd().endsWith(":")?"    ":"");
          event.preventDefault();input.setRangeText("\n"+indent,input.selectionStart,input.selectionEnd,"end");changed();
        }
      });
      if(pending()||source.editor_unchecked)drawDraft();
      const line=Math.max(1,state.focusLine||1),offset=input.value.split("\n").slice(0,line-1).reduce((sum,text)=>sum+text.length+1,0),position=idePositions.get(source.path);
      input.setSelectionRange(Math.min(position?.start??offset,input.value.length),Math.min(position?.end??offset,input.value.length));
      editor.scrollTop=position?.top??Math.max(0,(line-4)*24);editor.scrollLeft=position?.left??0;
      if(restoreIdeFocus)input.focus({preventScroll:true});
    }
    function invalidateEvidence(){
      closeInferences();
      root.querySelectorAll(".lr-inline-inferences,.lr-definition-references,.lr-diagnostics").forEach(node=>node.remove());
      root.querySelectorAll(".lr-book-heading .lr-badge,.lr-book-heading .lr-origin-note").forEach(node=>node.remove());
      const heading=root.querySelector(".lr-book-heading");
      if(heading&&!heading.querySelector(".lr-pending"))heading.append(element("span","lr-pending",editText("待检查","Not checked")));
      const typeLabel=root.querySelector(".lr-type-label");if(typeLabel)typeLabel.textContent=editText("草稿","Draft");
      if(detailPane)detailPane.replaceChildren(element("p","lr-empty-note",editText("源码已修改，检查后显示新的数学含义和证明依据。","Source changed. Check it to see fresh mathematical meaning and proof grounds.")));
    }
    function lang(){return locale.startsWith("zh")?"zh":"en";}
    function t(key){return copy[lang()][key]||key;}
    function sourceTitle(source){
      for(const locale of [lang(),"en","zh"]){const title=source?.titles?.[locale];if(typeof title==="string"&&title.trim())return title;}
      return source?.path||"Litex Reading";
    }
    function statementPresentation(statement){
      const path=String(statement?.statement_kind||"").split("."),family=path[0],kind=path[path.length-1],entry=statementTypes[kind]||statementTypes[family];
      let mode={Fact:"fact",Definition:"definition",Trust:"trust",By:"proof",ReleaseAndExpand:"release",Register:"registration",Witness:"proof",ProofBlock:"proof",Command:"command"}[family]||"unknown";
      if(family==="Definition"&&path[1]==="DefineObj")mode="declaration";
      if(["DefThmStmt","DefStrategyStmt"].includes(kind))mode="proof";
      if(kind==="AxiomStmt")mode="trust";
      const hints={fact:"statementFactHint",definition:"statementDefinitionHint",declaration:"statementDeclarationHint",proof:"statementProofHint",release:"statementReleaseHint",registration:"statementRegistrationHint",trust:"statementTrustHint",command:"statementCommandHint",unknown:"typeUnavailable"};
      return {title:entry?.[lang()==="zh"?1:0]||t("statementDetails"),syntax:entry?.[2],mode,hint:t(entry?.[3]||hints[mode])};
    }
    function index(){
      sources=new Map(array(bundle.sources).map(value=>[value.id,value]));
      statements=new Map(array(bundle.statements).map(value=>[value.id,value]));
      statementsBySource=new Map();for(const value of statements.values()){if(!statementsBySource.has(value.source_id))statementsBySource.set(value.source_id,[]);statementsBySource.get(value.source_id).push(value);}
      facts=new Map(array(bundle.facts).map(value=>[value.id,value]));
      symbols=new Map(array(bundle.symbols).map(value=>[value.id,value]));
      rules=new Map(array(bundle.rules).map(value=>[value.id,value]));
      evidenceNodes=new Map(array(bundle.evidence_nodes).map(value=>[value.id,value.node]));
      inferences=new Map(array(bundle.inferences).map(value=>[value.id,value]));
      wellDefinedness=new Map(array(bundle.well_definedness).map(value=>[value.id,value]));
      occurrences=array(bundle.occurrences);
      referencesBySource=new Map();declarationsBySource=new Map();
      const spanKey=value=>[value.source_id,value.symbol_id,value.start_byte,value.end_byte].join("|"),definitions=new Set(occurrences.filter(value=>value.definition===true).map(spanKey)),seenUses=new Set();
      for(const occurrence of occurrences){
        const key=spanKey(occurrence);if(occurrence.definition!==false||definitions.has(key)||seenUses.has(key))continue;seenUses.add(key);
        if(!referencesBySource.has(occurrence.source_id))referencesBySource.set(occurrence.source_id,new Map());
        const sourceUses=referencesBySource.get(occurrence.source_id);if(!sourceUses.has(occurrence.symbol_id))sourceUses.set(occurrence.symbol_id,[]);sourceUses.get(occurrence.symbol_id).push(occurrence);
      }
      const seenDeclarations=new Set();
      for(const statement of statements.values()){
        const canonical=statement.source_statement_id||statement.id;
        let ids=array(statement.declaration_symbol_ids);
        if(!ids.length){
          ids=[...symbols.values()].filter(symbol=>symbol.definition_statement_id===canonical).map(symbol=>symbol.id);
          const model=statement.mathematics,names=model?.kind==="objects"?array(model.parameters).flatMap(param=>array(param.names)):model?.kind==="binding"?[model.name]:[];
          if(names.length)ids.push(...occurrences.filter(value=>value.source_id===statement.source_id&&value.statement_id===canonical&&value.definition&&names.includes(symbols.get(value.symbol_id)?.name)).map(value=>value.symbol_id));
        }
        for(const id of ids){const definition=occurrences.find(value=>value.source_id===statement.source_id&&value.statement_id===canonical&&value.symbol_id===id&&value.definition===true);if(!definition||seenDeclarations.has(spanKey(definition)))continue;seenDeclarations.add(spanKey(definition));if(!declarationsBySource.has(statement.source_id))declarationsBySource.set(statement.source_id,[]);declarationsBySource.get(statement.source_id).push(definition);}
      }
      symbolDefinitions=new Map();
      for(const symbol of symbols.values())if(statements.has(symbol.definition_statement_id))symbolDefinitions.set(symbol.id,statements.get(symbol.definition_statement_id));
      for(const statement of statements.values())for(const id of array(statement.declaration_symbol_ids))if(!symbolDefinitions.has(id))symbolDefinitions.set(id,statements.get(statement.source_statement_id)||statement);
      for(const occurrence of occurrences)if(occurrence.definition&&!symbolDefinitions.has(occurrence.symbol_id)&&statements.has(occurrence.statement_id))symbolDefinitions.set(occurrence.symbol_id,statements.get(occurrence.statement_id));
      // Parameter groups carry resolved symbol identities. Keep the declared
      // domain separate from any membership facts inferred later in a proof.
      symbolBindings=new Map();symbolParameters=new Map();
      for(const occurrence of occurrences)if(occurrence.definition&&!symbolBindings.has(occurrence.symbol_id))symbolBindings.set(occurrence.symbol_id,occurrence);
      for(const node of evidenceNodes.values())if(node?.type==="TypedParameterGroup"){
        const type=resolveEvidence(node.fields?.param_type),domain=resolveEvidence(type.fields?.["0"]);
        const kind={Obj:"element",Set:"set",NonemptySet:"nonempty_set",FiniteSet:"finite_set"}[type.variant];
        if(!kind||kind==="element"&&typeof domain.text!=="string")continue;
        for(const parameter of array(node.fields?.params))if(parameter.kind==="symbol_reference"&&!symbolParameters.has(parameter.symbol_id))symbolParameters.set(parameter.symbol_id,{names:[parameter.name],kind,domain:domain.text});
      }
      // Only names belonging to a recorded export and resolved symbol can be
      // shortened. Ambiguous names outside the current source stay qualified.
      displayNames=new Map();
      const configurations=new Map(array(bundle.configurations).map(value=>[value.id,value.configuration]));
      const byName=new Map();for(const symbol of symbols.values()){if(!byName.has(symbol.name))byName.set(symbol.name,new Set());byName.get(symbol.name).add(symbol.id);}
      for(const source of sources.values()){
        const names=new Map(),config=configurations.get(source.configuration_id);
        for(const [i,entry] of array(config?.exports).entries())for(const symbol of symbols.values()){
          if(!["export:"+entry.path+":"+symbol.name,"named:"+entry.path+":"+symbol.name].includes(symbol.id))continue;
          const local=[...(byName.get(symbol.name)||[])].filter(id=>symbolDefinitions.get(id)?.source_id===source.id);
          if(local.length?local.length!==1||local[0]!==symbol.id:byName.get(symbol.name)?.size!==1)continue;
          names.set("f"+i+"::"+symbol.name,symbol.name);names.set(entry.name+"::"+symbol.name,symbol.name);
        }
        displayNames.set(source.id,names);
      }
      symbolRoles=new Map();
      for(const symbol of symbols.values()){
        const kind=symbol.kind;
        symbolRoles.set(symbol.id,symbol.id.startsWith("builtin:set:")?"type":["DefPropStmt","DefAbstractPropStmt"].includes(kind)?"predicate":["DefThmStmt","AxiomStmt","DefStrategyStmt"].includes(kind)?"theorem":["DefStructStmt","DefTemplateStmt"].includes(kind)?"type":"object");
      }
      for(const statement of statements.values())if(["HaveFnEqualStmt","HaveFnEqualCaseByCaseStmt","HaveFnByInducStmt","HaveFnByForallExistUniqueStmt","DefAlgoByCasesStmt","DefAlgoByInducStmt"].includes(String(statement.statement_kind||"").split(".").at(-1)))for(const id of array(statement.declaration_symbol_ids))symbolRoles.set(id,"function");
      const assignRole=(id,kind)=>{if(id&&(!symbolRoles.has(id)||symbolRoles.get(id)==="object"))symbolRoles.set(id,kind);};
      const inspectRole=node=>{
        if(node.type==="FnObjHead"&&node.variant==="Identifier")assignRole(node.fields?.["0"]?.symbol_id,"function");
        if(["NormalAtomicFact","NotNormalAtomicFact"].includes(node.type))assignRole(node.fields?.predicate?.symbol_id,"predicate");
      };
      const seenRoles=new Set();for(const statement of statements.values())walkEvidence(statement.evidence,inspectRole,seenRoles);
      if(!statements.size)rulebookState.usedOnly=false;
      usedRules=new Map();
      for(const statement of statements.values())for(const id of statementRules(statement)){if(!usedRules.has(id))usedRules.set(id,new Set());usedRules.get(id).add(statement.id);}
      if(!sources.has(state.source))state.source=sources.has(bundle.entry_source_id)?bundle.entry_source_id:sources.keys().next().value||null;
      if(!statements.has(state.statement)){state.statement=initialStatement(state.source)?.id||null;state.focusLine=statements.get(state.statement)?.line||null;}
    }
    function initialStatement(sourceId){const entries=statementsBySource.get(sourceId)||[];return entries.find(value=>value.status==="accepted"&&array(value.cited_fact_ids).length)||entries[0];}
    function walkEvidence(value,callback,seen=new Set()){
      const pending=[value];
      while(pending.length){const node=pending.pop();if(!node||typeof node!=="object")continue;callback(node);
        if(node.kind==="evidence_reference"){const key="evidence:"+node.evidence_id;if(!seen.has(key)){seen.add(key);pending.push(evidenceNodes.get(node.evidence_id));}}
        else if(node.kind==="statement_reference"){const key="statement:"+node.statement_id;if(!seen.has(key)){seen.add(key);pending.push(statements.get(node.statement_id)?.evidence);}}
        else pending.push(...(Array.isArray(node)?node:Object.values(node)).slice().reverse());
      }
    }
    function statementRules(statement){if(Array.isArray(statement.rule_ids))return new Set(statement.rule_ids);const applied=new Set();walkEvidence(statement.evidence,node=>{if(node.rule_id)applied.add(node.rule_id);});return applied;}
    function resolveEvidence(value){const seen=new Set();while(value?.kind==="evidence_reference"){if(seen.has(value.evidence_id))return {kind:"unavailable"};seen.add(value.evidence_id);value=evidenceNodes.get(value.evidence_id);}return value||{kind:"unavailable"};}
    function factLocation(fact){const producer=statements.get(fact?.producer_statement_id);if(factInferences(fact?.id).length&&producer)return {sourceId:producer.source_id,line:producer.line};return {sourceId:fact?.source_id||producer?.source_id,line:fact?.line||producer?.line};}
    async function navigate(next, remember=true){
      const serial=++navigationSerial,epoch=generation;
      const sourceId=statements.get(next.statement)?.source_id||next.source||state.source;
      try{
        if(loader&&sources.has(sourceId)&&typeof sources.get(sourceId).content!=="string"){
          operationStatus=t("loading");operationError=false;render();
          const chunk=await loader.loadSource(sourceId);
          if(destroyed||epoch!==generation)return false;
          mergeReadingChunk(bundle,chunk);index();
          if(serial!==navigationSerial)return false;
        }
        if(loader&&next.symbol&&!allOccurrencesLoaded){
          operationStatus=t("loadingIndex");operationError=false;render();
          const part=await loader.loadOccurrences();
          if(destroyed||epoch!==generation)return false;
          mergeReadingChunk(bundle,part);allOccurrencesLoaded=true;index();
          if(serial!==navigationSerial)return false;
        }
        const declaration=next.symbol&&symbolDefinitions.get(next.symbol),definitionSource=declaration&&sources.get(declaration.source_id);
        if(loader&&definitionSource&&typeof definitionSource.content!=="string"){
          const chunk=await loader.loadSource(definitionSource.id);if(destroyed||epoch!==generation)return false;
          mergeReadingChunk(bundle,chunk);index();if(serial!==navigationSerial)return false;
        }
      }catch(error){if(epoch===generation&&serial===navigationSerial&&!destroyed){operationStatus=t("loadFailed")+": "+error.message;operationError=true;render();}return false;}
      if(destroyed||epoch!==generation||serial!==navigationSerial)return false;
      operationStatus="";operationError=false;
      if(remember)history.push({...state});
      state={...state,reference:null,keyword:null,...next};
      if(next.statement){const statement=statements.get(next.statement);if(statement)state.source=statement.source_id;}
      render();
      if(state.focusLine)root.querySelector('[data-line="'+state.focusLine+'"]')?.scrollIntoView({block:"nearest",behavior:"smooth"});
      if(options.onNavigate)options.onNavigate({...state},{bundle_id:bundle.bundle_id||null});
      return true;
    }
    function selectStatement(id,line){return navigate({statement:id,symbol:null,fact:null,wd:null,focusLine:line||statements.get(id)?.line});}
    function selectSymbol(id){return navigate({symbol:id,fact:null,wd:null,focusLine:null});}
    function referenceUses(symbolId,sourceId){return (referencesBySource.get(sourceId)?.get(symbolId)||[]).slice().sort((a,b)=>a.start_byte-b.start_byte);}
    function occurrenceLocation(occurrence){
      const source=sources.get(occurrence.source_id),content=source?.content;if(typeof content!=="string")return null;
      const offsets=bytePositions(content),start=offsets.get(occurrence.start_byte),end=offsets.get(occurrence.end_byte);if(start===undefined||end===undefined)return null;
      const lineStart=content.lastIndexOf("\n",start-1)+1,next=content.indexOf("\n",end),lineEnd=next<0?content.length:next;
      return {line:content.slice(0,start).split("\n").length,before:content.slice(lineStart,start),token:content.slice(start,end),after:content.slice(end,lineEnd)};
    }
    function openReferences(symbolId,sourceId,opener){
      closeInferences();
      root.querySelector(".lr-references-dialog")?.remove();
      const dialog=element("dialog","lr-references-dialog"),name=symbols.get(symbolId)?.name||"",uses=referenceUses(symbolId,sourceId),title=t("referenceFor").replace("{name}",name);
      dialog.setAttribute("aria-label",title);const header=element("div","lr-help-heading"),close=button(t("closeReferences"),"lr-math-link",()=>dialog.close());header.append(element("strong",null,title),close);dialog.append(header,element("p","lr-reference-summary",t("currentFileReferences").replace("{count}",uses.length)),element("p","lr-empty-note",t("referenceHelp")));
      if(!uses.length)dialog.append(element("p","lr-empty-note",t("noReferences")));
      for(const occurrence of uses){const location=occurrenceLocation(occurrence);if(!location)continue;
        const link=button("","lr-reference-location",()=>{dialog.close();navigate({source:sourceId,statement:statements.has(occurrence.statement_id)?occurrence.statement_id:null,symbol:null,fact:null,wd:null,focusLine:location.line,reference:occurrence});});
        const snippet=element("code");snippet.append(document.createTextNode(location.before),element("mark",null,location.token),document.createTextNode(location.after));link.append(element("span","lr-reference-line",t("referenceLine").replace("{line}",location.line)),snippet);dialog.append(link);
      }
      dialog.addEventListener("close",()=>{dialog.remove();if(opener.isConnected)opener.focus();});dialog.addEventListener("click",event=>{if(event.target===dialog){const box=dialog.getBoundingClientRect();if(event.clientX<box.left||event.clientX>box.right||event.clientY<box.top||event.clientY>box.bottom)dialog.close();}});root.append(dialog);dialog.showModal();close.focus();
    }
    function closeInferences(restoreFocus=false){
      if(!inferencePopover)return;
      const {node,owner}=inferencePopover;inferencePopover=null;node.remove();owner.setAttribute("aria-expanded","false");owner.removeAttribute("aria-controls");
      if(restoreFocus&&owner.isConnected)owner.focus({preventScroll:true});
    }
    function positionInferences(){
      if(!inferencePopover)return;
      const {node,owner}=inferencePopover,box=owner.getBoundingClientRect(),view=document.documentElement,pane=(owner.closest(".lr-ide")||codePane).getBoundingClientRect();
      if(!owner.isConnected||box.bottom<Math.max(0,pane.top)||box.top>Math.min(view.clientHeight,pane.bottom)){closeInferences();return;}
      const bounds=node.getBoundingClientRect();
      node.style.left=Math.max(8,Math.min(box.left,view.clientWidth-bounds.width-8))+"px";
      node.style.top=Math.max(8,box.bottom+8+bounds.height<=view.clientHeight?box.bottom+8:box.top-bounds.height-8)+"px";
    }
    function openInferences(ids,sourceId,owner){
      const same=inferencePopover?.owner===owner;closeInferences();if(same)return;hideTokenHelp();
      const panel=element("div","lr-inference-popover"),id="lr-inferences-"+Math.random().toString(36).slice(2),heading=element("div","lr-inference-heading");
      panel.id=id;panel.setAttribute("role","dialog");panel.setAttribute("aria-label",t("inferredFacts"));
      const close=button("×","lr-inference-close",()=>closeInferences(true));close.setAttribute("aria-label",t("closeInferences"));
      heading.append(element("strong",null,t("inferredFacts")+" · "+ids.length),close);panel.append(heading);
      for(const factId of ids){
        const fact=facts.get(factId),result=button(displayText(fact.text,sourceId),"lr-inferred-result",()=>selectFact(factId));
        result.dataset.fact=factId;result.setAttribute("aria-label",t("inferred")+" "+displayText(fact.text,sourceId));
        if(factId===state.fact)result.classList.add("lr-inferred-selected");
        panel.append(result);
      }
      owner.setAttribute("aria-expanded","true");owner.setAttribute("aria-controls",id);root.append(panel);inferencePopover={node:panel,owner};positionInferences();
      panel.querySelector(".lr-inferred-result")?.focus({preventScroll:true});
    }
    function factInferences(id){return array(facts.get(id)?.inference_ids).map(key=>inferences.get(key)).filter(Boolean);}
    function statementInferredFacts(statement){const published=new Set(array(statement?.produced_fact_ids));return array(statement?.inferred_fact_ids).filter(id=>published.has(id));}
    function inferenceOrigins(id){return factInferences(id).flatMap(inference=>array(inference.conclusion_origins).filter(origin=>origin.fact_id===id));}
    function inferenceOriginLabel(origin){
      const name=symbols.get(origin.source_symbol_id)?.name;
      if(origin.kind==="definition")return name?t("fromNamedDefinition").replace("{name}",name):t("fromDefinition");
      if(origin.kind==="parameter_type")return name?t("fromNamedParamType").replace("{name}",name):t("fromParamType");
      return origin.rule_id?t("fromRule").replace("{name}",ruleTitle(origin.rule_id)):t("originUnavailable");
    }
    function appendInferenceOrigins(target,id,interactive){
      const origins=inferenceOrigins(id);
      if(!origins.length){target.append(element("small","lr-inference-origin",t("originUnavailable")));return;}
      for(const origin of origins){
        const title=inferenceOriginLabel(origin),definition=statements.get(origin.definition_statement_id);
        const action=definition?()=>selectStatement(definition.id):rules.has(origin.rule_id)?()=>showRule(origin.rule_id):null;
        const note=interactive&&action?button(title,"lr-origin-link",action):element("small","lr-inference-origin",title);
        if(definition)note.title=sourceTitle(sources.get(definition.source_id))+" · "+t("sourceLine")+" "+definition.line;
        target.append(note);
      }
    }
    function selectFact(id){const fact=facts.get(id);if(!fact)return false;const producer=statements.get(fact.producer_statement_id),location=factLocation(fact);return navigate({statement:producer?.id||null,source:producer?.source_id||(sources.has(location.sourceId)?location.sourceId:state.source),symbol:null,fact:id,wd:null,focusLine:producer?(location.sourceId===producer.source_id?location.line:producer.line):(sources.has(location.sourceId)?location.line:null)});}
    function selectWellDefinedness(id){const record=wellDefinedness.get(id);if(!record)return false;const producer=statements.get(record.producer_statement_id);return navigate({statement:producer?.id||null,source:producer?.source_id||state.source,symbol:null,fact:null,wd:id,focusLine:producer?.line||null});}
    function wdCitations(record){const cited=new Set(factCitations({evidence:record?.evidence}));if(facts.has(record?.source_fact_id))cited.add(record.source_fact_id);return [...cited];}
    function factCitations(fact){const cited=new Set(),inferred=factInferences(fact?.id),outputs=new Set(inferred.flatMap(value=>array(value.fact_ids)));for(const inference of inferred)cited.add(inference.source_fact_id);for(const evidence of inferred.length?inferred.map(value=>value.evidence):[fact?.evidence])walkEvidence(evidence,node=>{if(node.kind==="fact_reference"&&node.fact_id!==fact?.id&&!outputs.has(node.fact_id)&&facts.has(node.fact_id))cited.add(node.fact_id);});return [...cited];}
    function ruleTitle(id){
      const rule=rules.get(id),friendly=rule?.category==="infer"&&rule?.family==="InferNormalAtomicFactResult"&&rule.variant==="ParamTypes"?t("parameterTypesRule"):rule?.category==="infer"&&["ExpandDefinition","Definition"].includes(rule?.variant)?t("definitionExpansionRule"):null;
      return rule?.labels?.[lang()]?.name||friendly||rule?.name||humanize(rule?.variant||id.split(".").pop());
    }
    function ruleMessage(id){const rule=rules.get(id);return rule?.labels?.[lang()]?.message||rule?.message||"";}
    function label(role){return roles[role]?.[lang()==="zh"?1:0]||humanize(role);}
    function badge(content,failed){return element("span","lr-badge"+(failed?" lr-badge-failed":""),content);}
    function section(title){const node=element("div","lr-section-label",title);detailPane.append(node);}
    function displayText(value,sourceId=state.source){
      const names=displayNames.get(sourceId);
      return String(value||"").replace(/[\p{L}_][\p{L}\p{N}_]*(?:::[\p{L}_][\p{L}\p{N}_]*)+/gu,name=>names?.get(name)||name);
    }
    function mathText(value,sourceId=state.source){return displayText(value,sourceId).replace(/<=>/g,"⇔").replace(/=>:?/g,"⇒").replace(/\$not_in\b/g,"∉").replace(/\$in\b/g,"∈").replace(/\$subset\b/g,"⊆").replace(/\$superset\b/g,"⊇").replace(/!=/g,"≠").replace(/<=/g,"≤").replace(/>=/g,"≥").replace(/\bforall\b/g,"∀").replace(/\bexist!/g,"∃!").replace(/\bexist\b/g,"∃").replace(/\$(?=[\p{L}_])/gu,"");}
    function formula(value,sourceId=state.source){return element("div","lr-formula",mathText(value,sourceId));}
    function latexFormula(value,display,sourceId=state.source){
      if(typeof value!=="string"||!global.katex?.render)return null;
      // Generated identifiers are escaped inside mathit; keep the surrounding
      // LaTeX structure intact, including scopes and every mathematical clause.
      value=value.replace(/\\mathit\{((?:\\_|[\p{L}\p{N}:_])+)\}/gu,(whole,name)=>{
        const plain=name.replace(/\\_/g,"_"),short=displayText(plain,sourceId);
        return short===plain?whole:"\\mathit{"+short.replace(/_/g,"\\_")+"}";
      });
      const node=element("div","lr-latex");
      // The retained display compiler uses a root gathered environment for
      // quantified comparisons. Align only that outer layout, never matrices.
      if(value.startsWith("\\begin{gathered}"))node.classList.add("lr-latex-gathered");
      // Fold only the display compiler's two-row outer alignment. Nested
      // environments (matrices, cases, etc.) keep their original layout.
      const aligned=/^\\begin\{aligned\}&([\s\S]*)\\end\{aligned\}$/.exec(value);
      if(aligned&&!aligned[1].includes("\\begin{")&&aligned[1].split("\\\\&").length===2){value=aligned[1].replace("\\\\&","\\ ");display=false;node.classList.add("lr-latex-inline");}
      try{global.katex.render(value,node,{displayMode:display,throwOnError:true,trust:false,strict:"ignore",maxExpand:500,maxSize:50,output:"htmlAndMathml"});return node;}catch(_){return null;}
    }
    function renderPredicateLatex(model,sourceId){
      const data=model.latex,domains=array(data?.parameters),clauses=array(data?.facts);
      const parameterCount=array(model.parameters).reduce((count,param)=>count+(typeof param==="string"?1:array(param.names).length),0);
      if(!clauses.length||clauses.length!==array(model.facts).length||domains.length!==parameterCount)return false;
      const domainNodes=domains.map(value=>latexFormula(value,false,sourceId)),clauseNodes=clauses.map(value=>latexFormula(value,true,sourceId));
      if([...domainNodes,...clauseNodes].some(value=>!value))return false;
      const linked=(node,id,className)=>{if(!facts.has(id)){node.classList.add(className);return node;}const link=button("","lr-math-fact "+className,()=>selectFact(id));link.append(node);if(id===state.fact){link.classList.add("lr-current-math");link.setAttribute("aria-current","true");}return link;};
      const conditions=predicateIntro(model,sourceId);
      if(domainNodes.length){const row=element("div","lr-predicate-domains");domainNodes.forEach((node,index)=>{const item=element("span","lr-domain-item");item.append(linked(node,array(model.parameter_fact_ids)[index],"lr-latex-domain"));if(index<domainNodes.length-1)item.append(element("span","lr-domain-comma",","));row.append(item);});conditions.append(row);}
      clauseNodes.forEach((node,index)=>{const row=element("div","lr-condition-row");row.append(element("span","lr-condition-join",index?"∧":""),linked(node,array(model.fact_ids)[index],"lr-latex-clause"));conditions.append(row);});return true;
    }
    function predicateIntro(model,sourceId){
      const intro=element("div","lr-iff-intro");
      intro.append(latexFormula(model.latex?.subject,false,sourceId)||formula(model.subject,sourceId));
      const conditions=element("div","lr-predicate-conditions");
      const body=element("div","lr-iff-body");
      body.append(latexFormula("\\Longleftrightarrow",false)||element("span","lr-equivalence-operator","⇔"),conditions);
      detailPane.append(intro,body);return conditions;
    }
    function mathFact(value,id,sourceId){
      if(!facts.has(id))return formula(value,sourceId);
      const node=button("","lr-math-fact",()=>selectFact(id));node.append(formula(value,sourceId));
      if(id===state.fact){node.classList.add("lr-current-math");node.setAttribute("aria-current","true");}return node;
    }
    function parameterText(group,sourceId){const names=array(group.names).join(", ");return group.kind==="element"?names+" ∈ "+mathText(group.domain,sourceId):names+" "+t({set:"setKind",nonempty_set:"nonemptySetKind",finite_set:"finiteSetKind"}[group.kind]||"unavailable");}
    function renderMath(model,sourceId=state.source){
      if(!model||typeof model!=="object")return false;
      if(["predicate_definition","predicate_equivalence"].includes(model.kind)&&model.latex){if(renderPredicateLatex(model,sourceId))return true;detailPane.append(element("p","lr-empty-note",t("typesettingUnavailable")));}
      const params=array(model.parameters);if(params.length&&!["predicate_definition","predicate_equivalence"].includes(model.kind)){section(t(model.kind==="objects"?"takeObjects":"parameterRange"));params.forEach((param,index)=>detailPane.append(mathFact(typeof param==="string"?param:parameterText(param,sourceId),array(model.parameter_fact_ids)[index],sourceId)));}
      const clauses=array(model.facts);
      if(["predicate_definition","predicate_equivalence"].includes(model.kind)){
        if(!clauses.length){detailPane.append(element("p","lr-empty-note",t("meaningUnavailable")));return true;}
        const conditions=predicateIntro(model,sourceId);
        if(params.length){const row=element("div","lr-predicate-domains");params.forEach((param,index)=>{const text=typeof param==="string"?param:array(param.names).join(", ")+(param.kind==="element"?" ∈ "+mathText(param.domain,sourceId):" : "+param.kind),item=element("span","lr-domain-item");item.append(mathFact(text,array(model.parameter_fact_ids)[index],sourceId));if(index<params.length-1)item.append(element("span","lr-domain-comma",","));row.append(item);});conditions.append(row);}
        clauses.forEach((fact,index)=>{const row=element("div","lr-condition-row");row.append(element("span","lr-condition-join",index?"∧":""),mathFact(fact,array(model.fact_ids)[index],sourceId));conditions.append(row);});return true;
      }
      if(model.kind==="abstract_predicate"){detailPane.append(formula(model.subject,sourceId),element("p","lr-empty-note",t("abstractMeaning")));return true;}
      if(model.kind==="objects"){
        const names=params.flatMap(param=>array(param.names)),values=array(model.values);if(values.length===names.length)values.forEach((value,index)=>detailPane.append(formula(names[index]+" = "+value,sourceId)));
        if(clauses.length){section(t("alsoSatisfies"));clauses.forEach(fact=>detailPane.append(formula(fact,sourceId)));}return true;
      }
      if(model.kind==="binding"){detailPane.append(formula(model.name+" = "+model.value,sourceId));return true;}
      if(model.kind==="function"){
        const domain=array(model.domain_facts);if(domain.length){section(t("alsoSatisfies"));domain.forEach(fact=>detailPane.append(formula(fact,sourceId)));}detailPane.append(formula(model.subject,sourceId));section(t("valueRange"));detailPane.append(formula(model.codomain,sourceId));return true;
      }
      if(model.kind==="fact"){detailPane.append(formula(model.subject,sourceId));return true;}
      if(model.kind==="facts"){clauses.forEach(fact=>detailPane.append(formula(fact,sourceId)));return true;}
      return false;
    }
    function statementEquivalence(statement){
      const meaning=statement?.mathematics;if(meaning?.kind!=="fact")return null;
      const candidates=[...inferences.values()].filter(inference=>inference.producer_statement_id===statement.id&&inference.mathematics?.kind==="predicate_equivalence"&&(inference.source_fact_id===meaning.subject_fact_id||facts.get(inference.source_fact_id)?.text===meaning.subject));
      return candidates.length===1?candidates[0].mathematics:null;
    }
    function definitionLinks(ids){
      const links=element("div","lr-math-links");for(const id of new Set(ids)){const target=statements.get(id);if(!target)continue;const name=[...symbols.values()].find(symbol=>symbol.definition_statement_id===(target.source_statement_id||target.id))?.name||statementPresentation(target).title;links.append(button(t("viewDefinition").replace("{name}",name),"lr-math-link",()=>selectStatement(id)));}if(links.childElementCount)detailPane.append(links);
    }
    function renderStatus(statement){if(statement?.status==="rejected")detailPane.append(element("p","lr-origin-note",t("unverifiedMeaning")));else if(statement?.status==="not_exported")detailPane.append(element("p","lr-empty-note",t("unexecutedMeaning")));if(statement)renderOrigin(statement);}

    function renderPropGuide(target){
      const guide=element("div","lr-prop-guide"),example=element("pre","lr-guide-example");
      example.append(element("code",null,"prop nonnegative(x R):\n    x >= 0\n\nby def $nonnegative(3)"));
      guide.append(element("p",null,t("propGuidePurpose")),element("p",null,t("propGuideUse")),element("div","lr-section-label",t("propGuideExample")),example,element("p",null,t("propGuideMeaning")),element("p",null,t("propGuideProof")));
      target.append(guide);
    }

    function referenceCard(name){
      const zh=lang()==="zh",own=(table)=>Object.prototype.hasOwnProperty.call(table,name)?table[name]:null,set=own(setOperatorHelp),builtin=own(builtinObjectHelp),keyword=own(keywordReference);
      if(set)return {kind:zh?"集合运算符":"Set operator",syntax:set[0],summary:set[zh?3:4],input:set[zh?1:2],example:set[5]};
      if(builtin)return {kind:zh?"函数":"Function",syntax:builtin[0],summary:builtin[zh?2:3],input:builtin[1],example:builtin[4]};
      if(keyword){const text=keyword[zh?"zh":"en"];return {kind:text[0],syntax:keyword.syntax,summary:text[1],notes:text[2],example:keyword.example,walkthrough:keyword.walkthrough?.[zh?"zh":"en"]};}
      return null;
    }
    function appendReference(target,card,compact=false){
      target.append(element("small","lr-reference-kind",card.kind),element("p","lr-reference-summary",card.summary),element("pre","lr-reference-syntax",card.syntax));
      if(card.input)target.append(element("small",null,lang()==="zh"?"输入与结果":"Inputs and result"),element("div","lr-builtin-domain",card.input));
      if(card.notes)target.append(element("p","lr-reference-notes",card.notes));
      if(card.example)target.append(element("small",null,lang()==="zh"?"例子":"Example"),element("pre","lr-reference-example",card.example));
      if(card.walkthrough){
        if(compact)target.append(element("small","lr-reference-hint",lang()==="zh"?"点击关键词查看例子的逐项解释。":"Click the keyword for a point-by-point explanation."));
        else{
          const explanation=element("dl","lr-reference-walkthrough");
          for(const [title,text,latex,plain] of card.walkthrough){
            const body=element("dd");body.append(element("p",null,text));
            if(latex)body.append(latexFormula(latex,true)||element("div","lr-formula",plain||latex));
            explanation.append(element("dt",null,title),body);
          }
          target.append(explanation);
        }
      }
    }
    function renderInspectorContents(){if(state.keyword&&referenceCard(state.keyword))appendReference(detailPane,referenceCard(state.keyword));else if(state.keyword==="prop")renderPropGuide(detailPane);else if(state.keyword){detailPane.append(element("p","lr-keyword-meaning",syntaxPhrases[state.keyword]?.[lang()==="zh"?0:1]||syntaxHelp[state.keyword]?.[lang()==="zh"?0:1]||t("typeUnavailable")));}else if(state.symbol)renderSymbol();else if(state.wd)renderWellDefinedness();else if(state.fact)renderFact();else if(!state.statement&&state.focusLine)renderSourceLine();else renderStatement();}

    function render(){
      if(destroyed)return;
      const previousInput=root.querySelector(".lr-ide-input"),previousEditor=root.querySelector(".lr-ide");
      restoreIdeFocus=previousInput===document.activeElement;
      if(previousInput&&previousEditor)idePositions.set(previousInput.dataset.sourcePath,{start:previousInput.selectionStart,end:previousInput.selectionEnd,top:previousEditor.scrollTop,left:previousEditor.scrollLeft});
      closeInferences();hideTokenHelp();root.replaceChildren();root.classList.add("lr-root");
      const toolbar=element("div","lr-toolbar");
      const titleBlock=element("div","lr-title-block");const heading=element("div","lr-book-heading");titleBlock.append(heading);toolbar.append(titleBlock);
      const actions=element("div","lr-toolbar-actions");
      const back=button("←","lr-button lr-back",async()=>{const previous=history.pop();if(previous&&!await navigate(previous,false))history.push(previous);});back.setAttribute("aria-label",t("back"));if(history.length)actions.append(back);
      const source=sources.get(state.source);
      heading.append(element("h1","lr-book-title",sourceTitle(source)));
      if(source?.editor_unchecked)heading.append(element("span","lr-pending",editText("本章待检查","Chapter not checked")));
      else if(sources.size)heading.append(badge(bundle.run_result==="success"?t("verified"):t("failed"),bundle.run_result!=="success"));
      const trustCount=array(bundle.trust_summary?.user_assumptions).length+array(bundle.trust_summary?.axioms).length;if(trustCount)heading.append(element("span","lr-origin-note",t("trust")+" · "+trustCount));
      const records=element("details","lr-records lr-reading-help"),recordsSummary=element("summary",null,t("readingHelp")),recordPanel=element("div","lr-record-panel"),recordActions=element("div","lr-record-actions");
      records.append(recordsSummary,recordPanel);
      recordPanel.append(element("p",null,t("hint")));
      const legend=element("div","lr-legend");for(const key of ["selectedLegend","premiseLegend","occurrenceLegend","inferred"])legend.append(element("span",null,t(key)));recordPanel.append(legend);
      recordPanel.append(element("p",null,t("recordExplanation")),element("p","lr-record-format",t("recordFileExplanation")),recordActions);
      if(options.onOpenFiles)actions.append(button(t("openFiles"),"lr-button lr-open-file",()=>{records.open=false;options.onOpenFiles();}));
      if(options.onOpenProject)recordActions.append(button(t("openProject"),"lr-button",()=>{records.open=false;options.onOpenProject();}));
      records.addEventListener("keydown",event=>{if(event.key==="Escape"&&records.open){records.open=false;recordsSummary.focus();event.stopPropagation();}});
      const advanced=element("details","lr-advanced-help");advanced.append(element("summary",null,t("advancedHelp")),button(t("rulebook"),"lr-math-link",()=>{if(!rulebook?.isConnected)renderRulebook();rulebook.open=true;records.open=false;rulebook.scrollIntoView({block:"nearest",behavior:"smooth"});}));recordPanel.append(advanced);
      const footer=element("footer","lr-reading-footer");footer.append(records);
      if(sources.size)renderBookNavigation(actions);toolbar.append(actions);root.append(toolbar);
      if(operationStatus){const notice=element("p",operationError?"lr-diagnostics":"lr-loading",operationStatus);notice.setAttribute("role",operationError?"alert":"status");root.append(notice);}
      if(array(bundle.diagnostics).length){const diagnostics=element("div","lr-diagnostics");diagnostics.setAttribute("role","status");for(const diagnostic of bundle.diagnostics)diagnostics.append(element("div",null,diagnostic.message||diagnostic.kind));root.append(diagnostics);}
      if(!sources.size){const empty=element("section","lr-empty");const mark=element("div","lr-empty-mark","∀");mark.setAttribute("aria-hidden","true");empty.append(mark,element("h2",null,t("empty")),element("p",null,t("emptyHint")));root.append(empty,footer);return;}
      const layout=element("div","lr-layout");
      const sourcePane=element("section","lr-source-pane");const header=element("div","lr-pane-header");header.append(element("span",null,options.onCheck?editText("编辑器","Editor"):t("source")));
      codePane=element("div","lr-code");sourcePane.append(header,codePane);
      const presentation=statementPresentation(statements.get(state.statement)),selectedFact=facts.get(state.fact);
      const typeTitle=state.keyword?state.keyword:state.symbol?t("concepts"):state.wd?t("wellDefined"):state.fact?t(factInferences(state.fact).length?"inferred":selectedFact?.role==="verified"?"verifiedFact":selectedFact?.role||"fact"):presentation.title;
      const syntax=state.keyword||state.symbol||state.wd||state.fact?typeTitle:presentation.syntax||typeTitle;
      const details=element("section","lr-details"),inspectorHeader=element("div","lr-pane-header lr-inspector-header");
      inspectorHeader.append(element("span","lr-inspector-title",state.keyword?editText("参考说明","Reference"):t("mathematicalMeaning")),element("span","lr-type-label",syntax));details.append(inspectorHeader);
      details.addEventListener("keydown",async event=>{if(event.key==="Escape"&&state.keyword){event.preventDefault();const keyword=state.keyword,line=state.focusLine;await selectStatement(state.statement,line);root.querySelector('.lr-code-row[data-line="'+line+'"] [data-keyword="'+keyword+'"]')?.focus();}});
      detailPane=element("div","lr-detail-body");detailPane.setAttribute("aria-live","polite");details.append(detailPane);layout.append(sourcePane,details);root.append(layout,footer);
      renderCode();renderInspectorContents();
      if(options.onCheck){renderEditor(source,sourcePane,header);if(pending())invalidateEvidence();
        if(checking)detailPane.replaceChildren(element("p","lr-loading",editText("正在检查…","Checking…")));
        if(editError)detailPane.replaceChildren(element("p","lr-diagnostics",editError));}
    }

    function owningStatement(sourceId,line,offset){
      const candidates=(statementsBySource.get(sourceId)||[]).filter(value=>value.line<=line&&value.end_byte>value.start_byte&&value.end_byte>offset);
      if(!candidates.length)return null;
      const width=candidates.reduce((size,value)=>Math.min(size,value.end_byte-value.start_byte),Infinity);
      const narrow=candidates.filter(value=>value.end_byte-value.start_byte===width);
      const selected=narrow.find(value=>value.id===state.statement);if(selected)return selected;
      const ancestors=new Set();let current=statements.get(state.statement);while(current&&!ancestors.has(current.id)){ancestors.add(current.id);current=statements.get(current.parent_statement_id);}
      return narrow.find(value=>ancestors.has(value.parent_statement_id))||narrow.find(value=>value.id===(value.source_statement_id||value.id))||narrow[0];
    }

    function selectBookLine(entry){
      bookOpen=false;return navigate({source:entry.source_id,statement:entry.statement_id||null,symbol:null,fact:null,wd:null,focusLine:entry.line});
    }

    function renderBookNavigation(target){
      const details=element("details","lr-book-nav");details.open=bookOpen??false;details.addEventListener("toggle",()=>{bookOpen=details.open;});details.append(element("summary",null,t("book")));
      const chapters=element("nav","lr-chapters");chapters.setAttribute("aria-label",t("chapters"));
      const dependencies=element("details","lr-book-dependencies");dependencies.open=sources.get(state.source)?.role==="dependency";const dependencyLinks=element("div","lr-chapters");let dependencyCount=0;
      for(const source of sources.values()){
        const link=button(sourceTitle(source),"lr-chapter"+(source.id===state.source?" lr-active-chapter":""),()=>{bookOpen=false;const first=initialStatement(source.id);return navigate({source:source.id,statement:first?.id||null,symbol:null,fact:null,wd:null,focusLine:first?.line||1});});
        if(source.id===state.source)link.setAttribute("aria-current","page");
        if(source.role==="dependency"){dependencyLinks.append(link);dependencyCount++;}else chapters.append(link);
      }
      const panel=element("div","lr-book-panel");details.append(panel);
      // Optional host-authored links to independent reading bundles. Failed
      // examples must never be merged into the verified chapter sequence.
      for(const group of array(options.exampleGroups)){
        const links=element("nav","lr-chapters lr-extra-examples"),label=group.titles?.[lang()]||group.titles?.en||group.titles?.zh;
        if(!label)continue;links.setAttribute("aria-label",label);
        for(const entry of array(group.items)){
          if(typeof entry.href!=="string"||!entry.href||!/^(?:\.\.\/)*(?:[A-Za-z0-9_-]+\/)*$/.test(entry.href))continue;
          const title=entry.titles?.[lang()]||entry.titles?.en||entry.titles?.zh;if(!title)continue;
          const link=element("a","lr-chapter",title);link.href=entry.href+"?lang="+lang();links.append(link);
        }
        if(group.includeSources===true)links.prepend(...Array.from(chapters.childNodes));
        if(links.childElementCount){const category=element("section","lr-example-group");category.append(element("div","lr-section-label",label),links);panel.append(category);}
      }
      if(chapters.childElementCount)panel.append(chapters);if(dependencyCount){dependencies.append(element("summary",null,t("dependencies")+" · "+dependencyCount),dependencyLinks);panel.append(dependencies);}
      const tools=element("div","lr-book-search");bookSearch=element("input");bookSearch.type="search";bookSearch.placeholder=t("bookSearch");bookSearch.setAttribute("aria-label",t("bookSearch"));bookSearch.value=bookQuery;bookStatus=element("output","lr-empty-note");bookStatus.setAttribute("aria-live","polite");tools.append(bookSearch,bookStatus);bookResults=element("div","lr-book-results");panel.append(tools,bookResults);target.append(details);
      details.addEventListener("keydown",event=>{if(event.key==="Escape"){details.open=false;details.querySelector("summary").focus();}});
      bookSearch.addEventListener("input",()=>{bookQuery=bookSearch.value;bookPage=0;renderBookResults();});if(bookQuery)renderBookResults();
    }

    async function renderBookResults(){
      const serial=++bookSerial,epoch=generation,query=bookQuery.trim().toLowerCase();
      bookResults.replaceChildren();bookStatus.textContent="";if(!query)return;
      if(bookIndex===null){
        bookStatus.textContent=t("loadingIndex");
        try{
          if(loader){const part=await loader.loadSearch();if(destroyed||epoch!==generation)return;bookIndex=array(part.entries);}
          else{
            bookIndex=[];const encoder=new TextEncoder();
            for(const source of sources.values()){let offset=0;for(const [index,line] of String(source.content||"").split("\n").entries()){if(line.trim()){const owner=owningStatement(source.id,index+1,offset);bookIndex.push({source_id:source.id,line:index+1,text:line,statement_id:owner?.source_statement_id||owner?.id||null});}offset+=encoder.encode(line).length+1;}}
          }
        }catch(error){if(epoch===generation&&serial===bookSerial){bookStatus.textContent=t("loadFailed")+": "+error.message;}return;}
      }
      if(destroyed||epoch!==generation||serial!==bookSerial)return;
      const matches=bookIndex.filter(entry=>[entry.text,sourceTitle(sources.get(entry.source_id)),...Object.values(sources.get(entry.source_id)?.titles||{}).filter(value=>typeof value==="string"),sources.get(entry.source_id)?.path].join(" ").toLowerCase().includes(query));
      const pageSize=24,pages=Math.max(1,Math.ceil(matches.length/pageSize));bookPage=Math.min(bookPage,pages-1);bookStatus.textContent=matches.length?matches.length+" · "+(bookPage+1)+" / "+pages:t("noMatches");
      for(const entry of matches.slice(bookPage*pageSize,(bookPage+1)*pageSize)){
        const result=button("","lr-fact-link lr-book-result",()=>selectBookLine(entry));result.append(element("code",null,entry.text),element("small",null,sourceTitle(sources.get(entry.source_id))+" · "+t("sourceLine")+" "+entry.line));bookResults.append(result);
      }
      if(pages>1){const paging=element("div","lr-rule-paging"),previous=button("← "+t("previous"),"lr-button",()=>{bookPage--;renderBookResults();}),next=button(t("next")+" →","lr-button",()=>{bookPage++;renderBookResults();});previous.disabled=bookPage===0;next.disabled=bookPage+1>=pages;paging.append(previous,next);bookResults.append(paging);}
    }

    function renderSourceLine(){detailPane.append(element("p","lr-empty-note",t("noStatement")));}

    function hideTokenHelp(){if(tokenHelp){tokenHelp.node.remove();tokenHelp.owner.removeAttribute("aria-describedby");tokenHelp=null;}}
    function positionOverlays(){positionTokenHelp();positionInferences();}
    function positionTokenHelp(){
      if(!tokenHelp)return;const box=tokenHelp.owner.getBoundingClientRect(),tip=tokenHelp.node,rect=tip.getBoundingClientRect(),view=document.documentElement;
      if(box.bottom<0||box.top>view.clientHeight){hideTokenHelp();return;}
      tip.style.left=Math.max(8,Math.min(box.left,view.clientWidth-rect.width-8))+"px";
      tip.style.top=Math.max(8,box.bottom+8+rect.height<=view.clientHeight?box.bottom+8:box.top-rect.height-8)+"px";
    }
    function attachTokenHelp(token,heading,meaning,symbolId,builtin){
      token.setAttribute("aria-label",heading+" · "+meaning);
      function show(){
        if(tokenHelp?.owner===token)return;hideTokenHelp();
        const tip=element("div","lr-token-help"),id="lr-token-help-"+Math.random().toString(36).slice(2);tip.id=id;tip.setAttribute("role","tooltip");
        tip.append(element("strong",null,heading),element("span",null,meaning));
        const reference=!symbolId&&referenceCard(heading);if(reference){tip.replaceChildren(element("strong",null,heading));appendReference(tip,reference,true);}
        root.append(tip);token.setAttribute("aria-describedby",id);tokenHelp={node:tip,owner:token};
        if(symbolId){
          const declaration=symbolDefinitions.get(symbolId),info=element("div","lr-symbol-info");tip.append(info);
          const appendDefinition=()=>{
            info.replaceChildren();const data=definitionSource(symbolId),parameter=symbolParameters.get(symbolId);
            if(data){info.append(element("small",null,data.location));if(parameter)info.append(element("div","lr-symbol-domain",parameterText(parameter,data.sourceId)));info.append(element("pre","lr-definition-source",data.code));}
            info.append(element("small",null,t("currentFileReferences").replace("{count}",referenceUses(symbolId,state.source).length)));
            positionTokenHelp();
          };
          appendDefinition();
          if(loader&&declaration&&typeof sources.get(declaration.source_id)?.content!=="string"){
            const epoch=generation,loading=element("small",null,t("loading"));tip.append(loading);
            loader.loadSource(declaration.source_id).then(chunk=>{if(destroyed||epoch!==generation)return;mergeReadingChunk(bundle,chunk);index();if(tokenHelp?.node===tip&&token.isConnected){loading.remove();appendDefinition();}}).catch(()=>{if(tokenHelp?.node===tip)loading.textContent=t("loadFailed");});
          }
        }
        positionTokenHelp();
      }
      tokenHelpOpeners.set(token,show);
      token.addEventListener("mouseenter",show);token.addEventListener("focus",show);
      token.addEventListener("mouseleave",hideTokenHelp);token.addEventListener("blur",hideTokenHelp);
      token.addEventListener("keydown",event=>{if(event.key==="Escape")hideTokenHelp();});
    }
    function symbolHelp(id){
      if(!id.startsWith("builtin:set:"))return null;
      return standardSetHelp[id.slice("builtin:set:".length)]?.[lang()==="zh"?0:1]||null;
    }

    function renderCode(){
      const source=sources.get(state.source);if(!source)return;
      const content=source.content||"";const offsets=bytePositions(content);
      const sourceStatements=statementsBySource.get(source.id)||[];
      const selected=statements.get(state.statement);
      const citations=state.wd?wdCitations(wellDefinedness.get(state.wd)):state.fact?factCitations(facts.get(state.fact)):array(selected?.cited_fact_ids);
      const premiseLines=new Set(citations.map(id=>factLocation(facts.get(id))).filter(value=>value.sourceId===source.id).map(value=>value.line));
      function selectLine(owning,line){if(owning)selectStatement(owning.id,line);}
      const mentions=occurrences.filter(value=>value.source_id===source.id).map(value=>({...value,start:offsets.get(value.start_byte),end:offsets.get(value.end_byte)})).filter(value=>value.start!==undefined&&value.end!==undefined).sort((a,b)=>a.start-b.start);
      let mentionIndex=0;
      const lexical=array(source.tokens).map(value=>({...value,start:offsets.get(value.start_byte),end:offsets.get(value.end_byte)})).filter(value=>value.start!==undefined&&value.end!==undefined).sort((a,b)=>a.start-b.start).filter(value=>{while(mentionIndex<mentions.length&&mentions[mentionIndex].end<=value.start)mentionIndex++;return !mentions[mentionIndex]||mentions[mentionIndex].start>=value.end;});
      const declarationsAt=new Map();
      for(const declaration of declarationsBySource.get(source.id)||[]){const start=offsets.get(declaration.start_byte);if(start===undefined)continue;const line=content.slice(0,start).split("\n").length;if(!declarationsAt.has(line))declarationsAt.set(line,[]);declarationsAt.get(line).push(declaration);}
      const inferredAt=new Map();
      for(const statement of sourceStatements){
        const line=statement.line;
        for(const id of statementInferredFacts(statement))if(facts.has(id)&&factInferences(id).length){if(!inferredAt.has(line))inferredAt.set(line,[]);inferredAt.get(line).push(id);}
      }
      const hasTokens=array(source.tokens).length>0;
      function appendTrivia(target,text){if(hasTokens&&text.trim())target.append(element("span","lr-syntax-comment",text));else target.append(document.createTextNode(text));}
      let lineStart=0,lineByteStart=0;const encoder=new TextEncoder();
      const lines=content.split("\n");
      for(let i=0;i<lines.length;i++){
        const lineNumber=i+1,line=lines[i],lineEnd=lineStart+line.length;
        const owning=owningStatement(source.id,lineNumber,lineByteStart);
        const row=element("div","lr-code-row");row.dataset.line=String(lineNumber);if(owning)row.dataset.statement=owning.id;if(owning?.status==="rejected")row.classList.add("lr-rejected");
        if(state.focusLine?lineNumber===state.focusLine:owning?.id===state.statement)row.classList.add("lr-selected");else if(premiseLines.has(lineNumber))row.classList.add("lr-premise");
        const number=button(String(lineNumber),"lr-line-number",()=>selectLine(owning,lineNumber));number.disabled=!owning;number.setAttribute("aria-label",t("sourceLine")+" "+lineNumber);row.append(number);
        const lineContent=element("div","lr-code-content"),code=element("code","lr-source-code");let cursor=lineStart;
        const lineTokens=[...mentions.filter(value=>value.start>=lineStart&&value.end<=lineEnd),...lexical.filter(value=>value.start>=lineStart&&value.end<=lineEnd)].sort((a,b)=>a.start-b.start||Number(!!b.symbol_id)-Number(!!a.symbol_id)||Number(a.text==="$")-Number(b.text==="$"));
        const grouped=[];
        for(let j=0;j<lineTokens.length;j++){
          const first=lineTokens[j],next=lineTokens[j+1],phrase=first.text+" "+next?.text;
          if(!first.symbol_id&&next&&!next.symbol_id&&syntaxPhrases[phrase]&&/^[ \t]+$/.test(content.slice(first.end,next.start))){grouped.push({...first,text:phrase,end:next.end});j++;}else grouped.push(first);
        }
        for(const occurrence of grouped){
          if(occurrence.start<cursor)continue;
          appendTrivia(code,content.slice(cursor,occurrence.start));
          const spelling=content.slice(occurrence.start,occurrence.end);
          if(!occurrence.symbol_id){
            const role=(setOperatorHelp[occurrence.text]?"operator":syntaxPhrases[occurrence.text]?"keyword":lexicalKinds.get(occurrence.text))||(/^\d+(?:\.\d+)?$/.test(occurrence.text)?"number":"identifier"),token=element("span","lr-syntax-"+role,spelling);token.dataset.syntax=role;
            const builtin=builtinObjectHelp[occurrence.text],reference=referenceCard(occurrence.text),help=reference?.summary||builtin?.[lang()==="zh"?2:3]||(syntaxPhrases[occurrence.text]|| (Object.prototype.hasOwnProperty.call(syntaxHelp,occurrence.text)?syntaxHelp[occurrence.text]:syntaxRoleHelp[role]))?.[lang()==="zh"?0:1];
            if(help){token.tabIndex=0;attachTokenHelp(token,spelling,help,null,builtin);if(reference||syntaxPhrases[occurrence.text]||(role==="keyword"&&syntaxHelp[occurrence.text])){token.setAttribute("role","button");token.dataset.keyword=occurrence.text;token.setAttribute("aria-expanded",String(state.keyword===occurrence.text&&state.focusLine===lineNumber));const open=async()=>{if(state.keyword===occurrence.text&&state.focusLine===lineNumber){await selectStatement(owning?.id,lineNumber);root.querySelector('.lr-code-row[data-line="'+lineNumber+'"] [data-keyword="'+occurrence.text+'"]')?.focus();}else{await navigate({keyword:occurrence.text,statement:owning?.id||null,symbol:null,fact:null,wd:null,focusLine:lineNumber});detailPane.tabIndex=-1;detailPane.focus({preventScroll:true});}};token.addEventListener("click",event=>{event.stopPropagation();open();});token.addEventListener("keydown",event=>{if(["Enter"," "].includes(event.key)){event.preventDefault();open();}});}}code.append(token);cursor=occurrence.end;continue;
          }
          const role=symbolRoles.get(occurrence.symbol_id)||"object",token=button(spelling,"lr-token lr-syntax-"+role,event=>{event.stopPropagation();selectSymbol(occurrence.symbol_id);});token.dataset.symbol=occurrence.symbol_id;token.dataset.syntax=role;
          const builtinMeaning=symbolHelp(occurrence.symbol_id),meaning=builtinMeaning||syntaxRoleHelp[role]?.[lang()==="zh"?0:1];if(builtinMeaning)token.classList.add("lr-builtin-symbol");if(meaning)attachTokenHelp(token,spelling,meaning,occurrence.symbol_id);
          if(occurrence.symbol_id===state.symbol)token.classList.add("lr-symbol-selected");
          if(state.reference&&occurrence.symbol_id===state.reference.symbol_id&&occurrence.source_id===state.reference.source_id&&occurrence.start_byte===state.reference.start_byte&&occurrence.end_byte===state.reference.end_byte)token.classList.add("lr-reference-selected");
          code.append(token);cursor=occurrence.end;
        }
        appendTrivia(code,content.slice(cursor,lineEnd)||(!line?" ":""));lineContent.append(code);code.addEventListener("click",()=>selectLine(owning,lineNumber));
        const declarations=declarationsAt.get(lineNumber)||[];
        if(declarations.length){const counts=element("span","lr-definition-references");for(const declaration of declarations){const uses=referenceUses(declaration.symbol_id,source.id),name=symbols.get(declaration.symbol_id)?.name||"",label=t("referenceCount").replace("{count}",uses.length);const count=button((declarations.length>1?name+" · ":"")+label,"lr-reference-count",()=>openReferences(declaration.symbol_id,source.id,count));count.dataset.symbol=declaration.symbol_id;count.setAttribute("aria-label",t("referenceFor").replace("{name}",name)+" · "+label);counts.append(count);}lineContent.append(counts);}
        const inferredIds=[...new Set(inferredAt.get(lineNumber)||[])];
        if(inferredIds.length){
          const results=element("span","lr-inline-inferences");results.setAttribute("role","group");results.setAttribute("aria-label",t("inferredFacts"));
          const toggle=button(t("inferredCount").replace("{count}",inferredIds.length),"lr-inference-toggle",()=>openInferences(inferredIds,source.id,toggle));
          toggle.dataset.facts=JSON.stringify(inferredIds);toggle.setAttribute("aria-expanded","false");toggle.setAttribute("aria-haspopup","dialog");
          if(inferredIds.includes(state.fact))toggle.classList.add("lr-inferred-selected");else if(inferredIds.some(id=>citations.includes(id)))toggle.classList.add("lr-inferred-premise");
          results.append(toggle);
          lineContent.append(results);
        }
        row.append(lineContent);codePane.append(row);lineStart=lineEnd+1;lineByteStart+=encoder.encode(line).length+1;
      }
      const selectedInference=codePane.querySelector(".lr-inferred-selected"),selectedMarker=selectedInference||codePane.querySelector(".lr-reference-selected"),selectedRow=selectedMarker||codePane.querySelector(".lr-selected");if(selectedRow){const rowBounds=selectedRow.getBoundingClientRect(),paneBounds=codePane.getBoundingClientRect();if(rowBounds.bottom>paneBounds.bottom||rowBounds.top<paneBounds.top)codePane.scrollTop+=rowBounds.top-paneBounds.top-codePane.clientHeight/3;if(selectedMarker&&(rowBounds.right>paneBounds.right||rowBounds.left<paneBounds.left))codePane.scrollLeft+=rowBounds.left-paneBounds.left-64;}
    }

    function factButton(id){
      const fact=facts.get(id),node=button("","lr-fact-link"+(factInferences(id).length?" lr-inferred-link":""),()=>selectFact(id));node.append(formula(fact?.text||id,factLocation(fact).sourceId));
      if(fact?.role==="hypothesis")node.append(element("small",null,t("hypothesis")));if(!fact)node.disabled=true;return node;
    }

    function renderStatement(){
      const statement=statements.get(state.statement);if(!statement){detailPane.append(element("p","lr-empty-note",t("meaningUnavailable")));return;}
      const parent=statements.get(statement.parent_statement_id);if(parent)detailPane.append(button(t("outerProof"),"lr-math-link",()=>selectStatement(parent.id)));
      const instances=[...statements.values()].filter(value=>(value.source_statement_id||value.id)===(statement.source_statement_id||statement.id));if(instances.length>1){const contexts=element("div","lr-contexts");instances.forEach((instance,index)=>{const pick=button(t("context")+" "+(index+1),"lr-chip",()=>selectStatement(instance.id));pick.setAttribute("aria-pressed",String(instance.id===statement.id));contexts.append(pick);});detailPane.append(contexts);}
      const model=statementEquivalence(statement)||statement.mathematics;
      if(!renderMath(model)){
        const outputs=array(statement.produced_fact_ids).filter(id=>facts.has(id));if(outputs.length)outputs.forEach(id=>detailPane.append(factButton(id)));else detailPane.append(element("p","lr-empty-note",t("meaningUnavailable")));
      }
      if(statement.scope_id&&!String(statement.scope_id).startsWith("file:"))detailPane.append(element("p","lr-empty-note",t("underHypotheses")));
      renderStatus(statement);
      if(!["predicate_definition","predicate_equivalence","objects","binding","function","abstract_predicate"].includes(model?.kind)){
        const citations=array(statement.cited_fact_ids);if(citations.length){section(t("mathGrounds"));citations.forEach(id=>detailPane.append(factButton(id)));}
      }
      definitionLinks(array(statement.declaration_dependencies).filter(id=>id!==statement.id));
    }

    function renderFact(){
      const fact=facts.get(state.fact);if(!fact)return;if(factInferences(fact.id).length){renderInferredFact();return;}
      const producer=statements.get(fact.producer_statement_id),model=producer?.mathematics?.subject===fact.text?statementEquivalence(producer):null;
      if(!renderMath(model))detailPane.append(formula(fact.text,factLocation(fact).sourceId));
      if(fact.role==="hypothesis")detailPane.append(element("p","lr-empty-note",t("underHypotheses")));else if(fact.scope_id&&!String(fact.scope_id).startsWith("file:"))detailPane.append(element("p","lr-empty-note",t("local")));
      if(producer)renderOrigin(producer);
      const citations=factCitations(fact);if(!model&&citations.length){section(t("mathGrounds"));citations.forEach(id=>detailPane.append(factButton(id)));}
      if(producer)definitionLinks(array(producer.declaration_dependencies));
    }

    function renderInferredFact(){
      const fact=facts.get(state.fact),producer=statements.get(fact.producer_statement_id),batches=factInferences(fact.id),model=batches.map(batch=>batch.mathematics).find(value=>value?.kind==="predicate_equivalence");
      if(!renderMath(model)){detailPane.append(formula(fact.text,factLocation(fact).sourceId));const seeds=[...new Set(batches.map(batch=>batch.source_fact_id))];if(seeds.length){section(t("mathGrounds"));seeds.forEach(id=>detailPane.append(factButton(id)));}}
      if(fact.scope_id&&!String(fact.scope_id).startsWith("file:"))detailPane.append(element("p","lr-empty-note",t("underHypotheses")));if(producer)renderOrigin(producer);
      definitionLinks(inferenceOrigins(fact.id).map(origin=>origin.definition_statement_id));
    }

    function renderWellDefinedness(){
      const record=wellDefinedness.get(state.wd);if(!record)return;detailPane.append(formula(record.object),element("p","lr-empty-note",t("wellDefined")));
      const citations=wdCitations(record);if(citations.length){section(t("mathGrounds"));citations.forEach(id=>detailPane.append(factButton(id)));}
      const producer=statements.get(record.producer_statement_id);if(producer)renderOrigin(producer);
    }

    function renderOrigin(statement){
      if(statement.origin&&statement.origin!=="checked")detailPane.append(element("p","lr-origin-note",t(statement.origin)));
      const dependencies=array(statement.trust_dependencies);if(dependencies.length&&statement.origin==="checked"){const notice=element("div","lr-origin-note",t("trustUsed"));for(const id of dependencies){const target=statements.get(id);if(target)notice.append(button(t(target.origin),"lr-chip",()=>selectStatement(id)));}detailPane.append(notice);}
    }

    function definitionSource(id){
      const binding=symbolBindings.get(id),declaration=symbolDefinitions.get(id),source=sources.get(binding?.source_id||declaration?.source_id);
      if(typeof source?.content!=="string")return null;
      const offsets=bytePositions(source.content),local=!!symbolParameters.get(id)&&!(declarationsBySource.get(source.id)||[]).some(value=>value.symbol_id===id),record=local?binding:declaration;
      if(!record)return null;
      const start=offsets.get(record.start_byte),end=offsets.get(record.end_byte);
      if(start===undefined||end===undefined||end<=start)return null;
      const line=source.content.slice(0,start).split("\n").length;
      const code=local?source.content.split("\n")[line-1].trim():source.content.slice(start,end).trimEnd();
      return {location:sourceTitle(source)+" · "+t("referenceLine").replace("{line}",line),code,sourceId:source.id};
    }
    function renderSymbol(){
      const definition=definitionSource(state.symbol);
      if(definition){section(t("definition")+" · "+definition.location);detailPane.append(element("pre","lr-definition-source",definition.code));}
      const parameter=symbolParameters.get(state.symbol);if(parameter)detailPane.append(formula(parameterText(parameter,definition?.sourceId),definition?.sourceId));
      const mentions=occurrences.filter(value=>value.symbol_id===state.symbol),definitions=[...new Set(mentions.filter(value=>value.definition).map(value=>value.statement_id))];
      if(!definitions.length&&symbolDefinitions.has(state.symbol))definitions.push(symbolDefinitions.get(state.symbol).id);
      let shown=false;for(const id of definitions.filter(()=>!parameter||(declarationsBySource.get(definition?.sourceId)||[]).some(value=>value.symbol_id===state.symbol)))shown=renderMath(statements.get(id)?.mathematics,statements.get(id)?.source_id)||shown;
      if(!shown&&!parameter)detailPane.append(element("p","lr-empty-note",t("meaningUnavailable")));
      if(mentions.length){
        const disclosure=element("details","lr-occurrences"),body=element("div"),seen=new Set();
        for(const occurrence of mentions){const key=[occurrence.source_id,occurrence.start_byte,occurrence.end_byte].join("|");if(!seen.has(key)){seen.add(key);occurrenceButton(occurrence,body);}}
        disclosure.append(element("summary",null,t("references")+" · "+seen.size),body);detailPane.append(disclosure);
      }
    }

    function occurrenceButton(occurrence,target=detailPane){
      const source=sources.get(occurrence.source_id);if(!source)return;
      const statement=statements.get(occurrence.statement_id),location=occurrenceLocation(occurrence);
      const node=button("","lr-fact-link lr-occurrence-link",()=>navigate({source:occurrence.source_id,statement:occurrence.statement_id,symbol:null,fact:null,wd:null,focusLine:location?.line||statement?.line,reference:occurrence}));
      // Occurrences describe authored source, not execution-resolved subjects.
      // Keep explicit qualifications as written; never strip internal-looking names.
      const snippet=element("code");if(location)snippet.append(document.createTextNode(location.before.trimStart()),element("mark",null,location.token),document.createTextNode(location.after));
      else snippet.textContent=symbols.get(occurrence.symbol_id)?.name||t("unavailable");
      node.append(snippet,element("small",null,[sourceTitle(source),location?t("referenceLine").replace("{line}",location.line):null].filter(Boolean).join(" · ")));target.append(node);
    }

    function evidenceNode(value,title){
      value=resolveEvidence(value);
      if(value===null||value===undefined)return element("span","lr-empty-note","—");
      if(typeof value!=="object")return element("span","lr-evidence-subject",String(value));
      if(value.kind==="fact_reference")return factButton(value.fact_id);
      if(value.kind==="fact_identity")return element("span","lr-empty-note",value.fact_id);
      if(value.kind==="well_definedness_reference"||value.kind==="well_definedness_identity"){const record=wellDefinedness.get(value.id);const link=button(t("wellDefined")+" · "+(record?.object||value.id),"lr-fact-link",()=>selectWellDefinedness(value.id));link.disabled=!record;return link;}
      if(value.kind==="statement_reference"){const target=statements.get(value.statement_id);return button((target?.text||value.statement_id)+" · "+t("sourceLine")+" "+(target?.line||""),"lr-fact-link",()=>selectStatement(value.statement_id));}
      if(value.kind==="declaration_reference"){const target=statements.get(value.statement_id);const link=button((target?.text||t("definition"))+" · "+t("sourceLine")+" "+value.line,"lr-fact-link",()=>selectStatement(value.statement_id));link.disabled=!target;return link;}
      if(value.kind==="symbol_reference")return button(value.name||value.symbol_id,"lr-chip lr-concept-chip",()=>selectSymbol(value.symbol_id));
      if(value.kind==="scope")return element("span","lr-empty-note",t("local"));
      if(value.kind==="unavailable")return element("span","lr-empty-note",t("unavailable"));
      const details=element("details","lr-evidence");
      const route=routeNames[value.variant]?.[lang()==="zh"?1:0];
      const summary=element("summary",null,value.rule_id?ruleTitle(value.rule_id):(route||title||humanize(value.variant)||t("proof")));details.append(summary);
      details.addEventListener("toggle",()=>{
        if(!details.open||details.childElementCount>1)return;
        const body=element("div");if(value.text)body.append(element("code","lr-evidence-subject",value.text));
        if(value.rule_id){body.append(button(t("rulebook")+" ↗","lr-chip",()=>showRule(value.rule_id)));const message=ruleMessage(value.rule_id);if(message)body.append(element("p","lr-empty-note",message));}
        const entries=Array.isArray(value)?value.map((item,index)=>[String(index+1),item]):Object.entries(value.fields||value).filter(([key])=>!["text","type","variant","rule_id"].includes(key));
        for(const [key,item] of entries){if(item===null||(Array.isArray(item)&&!item.length))continue;body.append(element("div","lr-evidence-label",label(key)),evidenceNode(item,label(key)));}details.append(body);
      });
      return details;
    }

    function renderRulebook(){
      rulebook=element("details","lr-rulebook");rulebook.open=rulebookState.open;rulebook.addEventListener("toggle",()=>{rulebookState.open=rulebook.open;});rulebook.append(element("summary",null,t("rulebook")));
      const tools=element("div","lr-rulebook-tools");ruleSearch=element("input");ruleSearch.type="search";ruleSearch.placeholder=t("search");ruleSearch.setAttribute("aria-label",t("search"));
      ruleSearch.value=rulebookState.query;const usedLabel=element("label");usedOnly=element("input");usedOnly.type="checkbox";usedOnly.checked=rulebookState.usedOnly;usedLabel.append(usedOnly,document.createTextNode(" "+t("usedOnly")));tools.append(ruleSearch,usedLabel);rulebook.append(tools);
      const categories=element("select");categories.setAttribute("aria-label",t("category"));for(const category of ["all",...new Set([...rules.values()].map(rule=>rule.category).filter(Boolean))]){const option=element("option",null,category==="all"?t("allCategories"):t(category));option.value=category;option.selected=category===rulebookState.category;categories.append(option);}tools.insertBefore(categories,usedLabel);categories.addEventListener("change",()=>{rulebookState.category=categories.value;rulePage=0;renderRules();});
      ruleGrid=element("div","lr-rule-grid");paging=element("div","lr-rule-paging");rulebook.append(ruleGrid,paging);root.append(rulebook);
      ruleSearch.addEventListener("input",()=>{rulebookState.query=ruleSearch.value;rulePage=0;renderRules();});usedOnly.addEventListener("change",()=>{rulebookState.usedOnly=usedOnly.checked;rulePage=0;renderRules();});renderRules();
    }
    function renderRules(){
      const query=ruleSearch.value.trim().toLowerCase();const list=[...rules.values()].filter(rule=>(!usedOnly.checked||usedRules.has(rule.id))&&(rulebookState.category==="all"||rule.category===rulebookState.category)&&[rule.id,ruleTitle(rule.id),rule.variant,ruleMessage(rule.id)].join(" ").toLowerCase().includes(query));
      const pageSize=18;const pages=Math.max(1,Math.ceil(list.length/pageSize));rulePage=Math.min(rulePage,pages-1);ruleGrid.replaceChildren();paging.replaceChildren();
      for(const rule of list.slice(rulePage*pageSize,(rulePage+1)*pageSize)){
        const card=element("article","lr-rule-card"+(rule.id===activeRule?" lr-active-rule":""));card.dataset.rule=rule.id;card.append(element("h3",null,ruleTitle(rule.id)),element("p",null,ruleMessage(rule.id)||t("catalogueOnly")));
        for(const id of usedRules.get(rule.id)||[]){const statement=statements.get(id);card.append(button(t("sourceLine")+" "+statement.line,"lr-chip",()=>selectStatement(id)));}ruleGrid.append(card);
      }
      const previous=button("← "+t("previous"),"lr-button",()=>{rulePage--;renderRules();});previous.disabled=rulePage===0;
      const next=button(t("next")+" →","lr-button",()=>{rulePage++;renderRules();});next.disabled=rulePage+1>=pages;paging.append(previous,element("span",null,(rulePage+1)+" / "+pages+" · "+list.length),next);
    }
    function showRule(id){activeRule=id;rulebookState={query:id,usedOnly:false,open:true,category:"all"};rulebook.open=true;ruleSearch.value=id;usedOnly.checked=false;rulebook.querySelector("select").value="all";rulePage=0;renderRules();rulebook.scrollIntoView({block:"nearest",behavior:"smooth"});}

    const dismissPanels=event=>{if(inferencePopover&&!inferencePopover.node.contains(event.target)&&!inferencePopover.owner.contains(event.target))closeInferences();const records=root.querySelector(".lr-records");if(records?.open&&!records.contains(event.target))records.open=false;const menu=root.querySelector(".lr-book-nav");if(menu?.open&&!menu.contains(event.target))menu.open=false;};
    const dismissInferences=event=>{if(event.key==="Escape"&&inferencePopover){event.preventDefault();event.stopPropagation();closeInferences(true);}};
    document.addEventListener("pointerdown",dismissPanels);
    root.addEventListener("keydown",dismissInferences);
    window.addEventListener("scroll",positionOverlays,true);
    window.addEventListener("resize",positionOverlays);
    index();render();
    const api = {
      update(document,settings={}){if(!settings.preserveDrafts){drafts.clear();originals.clear();revision=0;checkedRevision=0;idePositions.clear();editError="";}if(document.kind==="reading_manifest")throw new Error("Use LitexReading.open for a manifest");generation++;navigationSerial++;bookSerial++;loader=null;allOccurrencesLoaded=true;bookIndex=null;bookQuery="";bookOpen=null;operationStatus="";bundle=document;history=[];state={source:null,statement:null,symbol:null,fact:null,wd:null,focusLine:null};activeRule=null;rulePage=0;rulebookState={query:"",usedOnly:true,open:false,category:"all"};index();render();if(options.onNavigate)options.onNavigate({...state},{bundle_id:bundle.bundle_id||null});},
      setLanguage(value){locale=value;render();},
      selectStatement(id){return statements.has(id)?selectStatement(id):false;},
      selectFact(id){return facts.has(id)?selectFact(id):false;},
      selectWellDefinedness(id){return wellDefinedness.has(id)?selectWellDefinedness(id):false;},
      getSelection(){return {...state};},
      getBundleId(){return bundle.bundle_id||null;},
      async getProjectSnapshot(){
        const snapshotSources=[];
        for(const source of sources.values()){
          if(typeof source.content==="string")snapshotSources.push({...source});
          else if(loader){const chunk=await loader.loadSource(source.id);snapshotSources.push({...source,...chunk.sources.find(item=>item.id===source.id)});}
        }
        return {sources:snapshotSources,configurations:bundle.configurations||[],strict:bundle.execution_policy?.strict===true};
      },
      destroy(){closeInferences();hideTokenHelp();window.removeEventListener("scroll",positionOverlays,true);window.removeEventListener("resize",positionOverlays);destroyed=true;generation++;navigationSerial++;bookSerial++;document.removeEventListener("pointerdown",dismissPanels);root.removeEventListener("keydown",dismissInferences);root.replaceChildren();}
    };
    return api;
  }
  function mergeReadingChunk(bundle,part){
    for(const key of ["sources","statements","facts","inferences","well_definedness","evidence_nodes","occurrences"]){
      if(!Array.isArray(part[key]))continue;
      const identity=value=>key==="occurrences"?[value.source_id,value.start_byte,value.end_byte,value.symbol_id,value.statement_id,value.definition].join("|"):value.id;
      const records=new Map(array(bundle[key]).map(value=>[identity(value),value]));
      for(const value of part[key]){const id=identity(value),existing=records.get(id);if(key==="evidence_nodes"&&existing&&JSON.stringify(existing.node)!==JSON.stringify(value.node))throw new Error("Conflicting reading evidence: "+id);records.set(id,{...existing,...value});}
      bundle[key]=[...records.values()];
    }
  }

  async function openReadingReader(root,source,options){
    options=options||{};
    const base=new URL(typeof source==="string"?source:options.baseUrl||location.href,document.baseURI);
    const fetchJSON=async(url,cache="default")=>{const response=await fetch(url,{cache});if(!response.ok)throw new Error("Reading HTTP "+response.status);return response.json();};
    const manifest=typeof source==="string"?await fetchJSON(base.href,"no-store"):source;
    if(manifest?.kind==="reading")return mountReadingReader(root,{...options,document:manifest});
    if(manifest?.kind!=="reading_manifest"||!["1","2"].includes(manifest.schema_version)||typeof manifest.manifest_id!=="string")throw new Error("Unsupported reading manifest");
    const localURL=path=>{const url=new URL(path,base);if(url.origin!==base.origin)throw new Error("Reading parts must share the manifest origin");return url.href;};
    const part=async(path,kind)=>{const value=await fetchJSON(localURL(path));if(value.kind!==kind||value.manifest_id!==manifest.manifest_id)throw new Error((options.locale||manifest.language||"").startsWith("zh")?copy.zh.changedBuild:copy.en.changedBuild);return value;};
    const sources=new Map(array(manifest.sources).map(value=>[value.id,value]));
    const pending=new Map();let occurrencePromise,searchPromise;
    const loader={
      loadSource(id){if(!pending.has(id)){const source=sources.get(id);if(!source)throw new Error("Unknown reading source");pending.set(id,part(source.chunk_url,"reading_chunk").then(value=>{if(value.source_id!==id||value.sources?.length!==1||value.sources[0].id!==id)throw new Error("Mismatched reading source");return value;}).catch(error=>{pending.delete(id);throw error;}));}return pending.get(id);},
      loadOccurrences(){return occurrencePromise||(occurrencePromise=part(manifest.occurrences_url,"reading_occurrences").catch(error=>{occurrencePromise=null;throw error;}));},
      loadSearch(){return searchPromise||(searchPromise=part(manifest.search_url,"reading_search").catch(error=>{searchPromise=null;throw error;}));},
      downloadUrl:localURL(manifest.full_document_url)
    };
    const bundle={...manifest,kind:"reading",sources:array(manifest.sources).map(value=>({...value})),evidence_nodes:[],occurrences:[]};
    const first=sources.has(manifest.entry_source_id)?manifest.entry_source_id:sources.keys().next().value;
    if(first){root.replaceChildren(element("p","lr-loading",(options.locale||manifest.language||"").startsWith("zh")?copy.zh.loading:copy.en.loading));mergeReadingChunk(bundle,await loader.loadSource(first));}
    return mountReadingReader(root,{...options,document:bundle,loader});
  }

  global.LitexReading=Object.freeze({mount:mountReadingReader,open:openReadingReader,schemaVersion:"2",supportedSchemaVersions:Object.freeze(["1","2"])});
})(window);
