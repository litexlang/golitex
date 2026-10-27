(() => {
  const evidence = JSON.parse(document.getElementById("verification-data").textContent);
  const stages = {
    en: [
      ["A goal in context", "have x R declares x to be a real number (x ∈ ℝ). The next fact asks whether 0 ≤ (x + 1)² follows from that context."],
      ["Check well-definedness", "Before truth search, check objects, the predicate signature and its domains. Those checks can themselves require mathematical evidence."],
      ["Select a builtin rule", "The selected order rule says that an even power of a real base is nonnegative. It requires evidence that x + 1 is real."],
      ["Resolve the real-base premise", "Direct structural membership follows the addition expression. Both operand memberships must hold; it does not reopen unrestricted proof search."],
      ["Retrieve the leaf evidence", "The left operand cites x ∈ ℝ from the declaration. Membership of the numeral 1 in ℝ is established by closed calculation."],
      ["Assemble and publish", "Combine the child evidence into the rule proof. Only after the top-level fact is verified is it stored and passed to direct inference once; this example yields no additional inferred facts."],
    ],
    zh: [
      ["目标与当前上下文", "have x R 声明 x 是一个实数（x ∈ ℝ）。下一行询问：从这个上下文，能否找到 0 ≤ (x + 1)² 的证明？"],
      ["先检查良定义性", "在搜索真值证据之前，检查对象、谓词签名和适用域。这些检查本身也可能需要数学证据。"],
      ["匹配内置规则", "本例选中的序关系规则是：实数的偶次幂非负。规则要求提供 x + 1 是实数的证据。"],
      ["继续检查实数前提", "Direct 结构性成员检查沿加法表达式向下分解，要求两个操作数都是实数；它不会重新开启无限制搜索。"],
      ["找到叶子证据", "左边引用声明产生的 x ∈ ℝ；右边通过闭式计算确认数值 1 属于 ℝ。"],
      ["组合并存储证据", "将子证据组合为规则证明。顶层事实验证成功后才存储，并直接推导一次；本例没有额外的推导事实。"],
    ],
  };
  const info = {
    goal: ["The query", "待验证事实", "A proposed fact is a query against the current context; it is not added to knowledge before verification succeeds.", "待验证事实是交给当前上下文的查询；验证成功之前，它不会被加入知识中。", "demo.lit:3"],
    context: ["Scoped mathematical knowledge", "带作用域的数学知识", "Visible scopes expose definitions, indexed facts, equalities and object properties. Source identities make citations inspectable. Imported definitions use their supported interfaces.", "可见作用域提供定义、索引事实、等式和对象属性；来源标识让引用可以追溯。导入定义通过其支持的接口使用。", "src/exec_env/README.md"],
    "context-fact": ["An established fact", "已建立的事实", "have x R declares x to be a real number and records x ∈ ℝ. The selected proof cites this fact without assigning x a particular numerical value.", "have x R 声明 x 是一个实数，并记录 x ∈ ℝ。选中证明引用这个事实，不需要给 x 指定某个具体数值。", `demo.lit:2 · ${evidence.context_fact_id}`],
    shape: ["Logical-shape dispatch", "按逻辑形状分派", "verify_fact dispatches to the appropriate fact family. Equality has its own atomic pipeline; panel b shows the non-equality route used by this example.", "verify_fact 按事实形状选择对应家族。等式有独立的原子事实管线；面板 b 展示本例使用的非等式入口。", "src/execute/execute_fact_stmt/verify.rs"],
    wd: ["Well-definedness", "良定义性", "Objects, predicate signatures and domains are checked before truth search. A missing formation/domain proof stops the fact before truth search.", "对象、谓词签名与适用域先于真值搜索检查；缺少表达式形成或适用域证据时，不会继续验证该事实的真值。", "src/execute/execute_fact_stmt/verify_atomic_fact/verify_atomic_except_equality/verify_atomic_except_equality.rs"],
    direct: ["Direct evidence", "直接证据", "Look up stored evidence, perform supported closed calculations, or follow deterministic structural memberships. Structural traversal has narrower permissions than general rule search.", "读取已存证据、执行支持的闭式计算，或沿结构确定性地检查成员关系。结构遍历的权限比一般规则搜索更窄。", "src/execute/execute_fact_stmt/verify_atomic_fact/verify_atomic_except_equality/search_atomic_except_equality_fact_proof_directly.rs"],
    known: ["Known facts and properties", "已知事实匹配与对象属性", "Try supported fact matching and exact-object property readers. This is an ordered search slot; it is not another level of mathematical truth.", "尝试支持的事实匹配与精确对象属性读取。这是一个有顺序的搜索入口，不是另一层数学真理。", "src/execute/execute_fact_stmt/verify_state.rs"],
    builtin: ["Builtin rule families", "内置规则家族", "Rules are selected by fact shape, such as equality, order or membership. Here an order rule asks a membership question; the premise is passed a KnownSpecialProperty ceiling with rewrite disabled.", "规则按事实形状选择，例如等式、序关系、成员关系。本例的序关系规则需要成员关系证据；前提的搜索上限为 KnownSpecialProperty，且禁止改写。", "VerifyState::for_premises(BuiltinRule) → KnownSpecialProperty"],
    strategy: ["Bounded strategies", "受约束的策略", "Supported compound checking routes may coordinate several obligations. Their ordinary premises inherit a BuiltinRule ceiling; this example succeeds earlier.", "支持的复合检查路径可以组织多个条件；普通前提继承 BuiltinRule 上限。本例在更早的入口已找到证据。", "VerifyState::for_premises(Strategy) → BuiltinRule"],
    definition: ["Definition paths", "定义路径", "Try the fact family's supported definition route. Equality and other atomic facts have distinct entry implementations. This example does not need this slot.", "尝试当前事实家族支持的定义路径。等式和其他原子事实的实现入口不同；本例不需要进入这一项。", "VerifyState::DefinitionAndForall"],
    forall: ["Known universal facts", "已知全称事实", "Match supported conclusions of stored universal facts and check instantiated premises. This is not an unrestricted search over every named theorem.", "匹配已存全称事实中受支持的结论，再检查实例化前提；这不等于自动搜索所有命名定理。", "src/execute/execute_fact_stmt/verify_atomic_fact/search_proof_by_known_forall_fact.rs"],
    rewrite: ["Final rewrite opportunity", "最后的改写机会", "A permitted final fallback tries supported replacements and checks the residual goal without reopening rewrite on that branch.", "允许的最后回退路径尝试支持的替换，再检查残余目标；该分支不会重新获得改写机会。", "VerifyState::after_rewrite"],
    miss: ["No proof found", "未找到证明", "A search miss does not prove the fact false and does not publish it as a known fact.", "搜索未命中，不表示命题为假，也不会将它发布为已知事实。", "ExecFactStmtResult::Failed"],
    proof: ["One successful route suffices", "一条成功路径即可", "The pipeline returns on a successful route. For this example the retained successful proof is the even-power builtin, with its checked real-base premise.", "管线在找到成功路径时返回。本例保留的是偶次幂非负规则及其已检查的实数底数前提。", evidence.rule_ids.join("\n")],
    result: ["The assembled conclusion", "组合得到的结论", "The returned proof includes formation evidence and the selected truth proof. The figure shows the main mathematical dependency, while leaving routine WD details in the underlying record.", "返回的证明包含表达式形成证据和选中的真值证明。图中展示主要数学依赖，常规良定义性细节保留在底层记录中。", "VerifyAtomicExceptEqualityFactSuccess"],
    square: ["An order builtin", "序关系内置规则", "EvenPowNonnegative requires a checked real base. The displayed square is an instance of that rule; complex formation alone would not establish the required real-base condition.", "EvenPowNonnegative 要求已检查的实数底数。本例的平方是它的一个实例；仅有复数表达式合法性，不能替代实数底数条件。", evidence.rule_ids[0]],
    real: ["A membership obligation", "成员关系条件", "The order rule asks for x + 1 ∈ ℝ. The retained proof of this premise uses Direct structural membership.", "序关系规则需要 x + 1 ∈ ℝ；这一前提的实际保留证据来自 Direct 结构性成员检查。", "ByStructuralMembership"],
    add: ["Structural addition", "按加法结构分解", "Real addition closure combines the two smaller membership proofs. This is Direct structural traversal, not a recursive re-entry into the BuiltinRule dispatcher.", "实数加法封闭性组合两个更小的成员关系证明。这是 Direct 结构遍历，不是递归重新进入 BuiltinRule 分派器。", "StructuralMembershipReason::Add"],
    x: ["The known left operand", "左操作数的已知证据", "The exact x ∈ ℝ membership is read from the established context, retaining the citation to the have declaration.", "从已建立的上下文读取 x ∈ ℝ，并保留对 have 声明的引用。", `StructuralMembershipReason::Known · ${evidence.context_fact_id}`],
    one: ["The closed right operand", "右操作数的闭式证据", "Membership of the literal 1 in ℝ is checked by supported exact closed calculation; it is not a new user assumption.", "字面量 1 属于 ℝ 由支持的精确闭式计算检查，不需要新增用户假设。", "StructuralMembershipReason::Closed"],
    lookup: ["A citation into the context", "对上下文的引用", "The successful leaf points to the established membership fact. Reusing a fact should retain its identity and source.", "成功的叶子节点指向已建立的成员关系事实。事实复用保留其身份与来源。", `Known.cite_fact_id = ${evidence.context_fact_id}`],
    calculation: ["Exact closed calculation", "精确闭式计算", "The numeral membership is closed and can be checked without choosing a theorem, a witness, or a new assumption.", "数值成员关系是闭式的，可直接检查；不需要选择定理、见证或增加假设。", "ClosedMembershipCalculationProof::StandardSet"],
    commit: ["Store, then direct inference", "先存储，再直接推导", "Once the top-level statement is accepted, its fact is indexed and direct inference runs once. Inferred conclusions do not automatically start another inference chain. This example has an empty infers list.", "顶层陈述接受后，将事实编入索引并直接推导一次；推导结论不会自动开启另一条推导链。本例的 infers 为空。", "src/store_fact_and_infer/README.md"],
  };
  let language = new URLSearchParams(location.search).get("lang") === "zh" ? "zh" : "en";
  let step = 0;
  let selected = "goal";
  let timer = null;
  const track = document.getElementById("step-track");
  const play = document.getElementById("play");
  const previous = document.getElementById("previous");
  const next = document.getElementById("next");

  function stop() {
    clearInterval(timer);
    timer = null;
    play.setAttribute("aria-pressed", "false");
    play.textContent = language === "zh" ? "播放" : "Play";
  }

  function render() {
    document.documentElement.lang = language === "zh" ? "zh-CN" : "en";
    document.querySelectorAll("[data-en]").forEach(node => { node.textContent = node.dataset[language]; });
    if (timer) play.textContent = language === "zh" ? "暂停" : "Pause";
    for (const lang of ["en", "zh"]) {
      document.getElementById(`figure-${lang}`).hidden = lang !== language;
      document.getElementById(`language-${lang}`).setAttribute("aria-pressed", String(lang === language));
    }
    document.getElementById("step-number").textContent = `${String(step+1).padStart(2,"0")} / 06`;
    document.getElementById("step-title").textContent = stages[language][step][0];
    document.getElementById("step-description").textContent = stages[language][step][1];
    previous.disabled = step === 0;
    next.disabled = step === 5;
    [...track.children].forEach((button, index) => {
      button.setAttribute("aria-pressed", String(index === step));
      button.setAttribute("aria-label", `${index+1}. ${stages[language][index][0]}`);
      button.classList.toggle("complete", index < step);
    });
    document.querySelectorAll(".node").forEach(node => {
      node.classList.toggle("is-current", node.dataset.steps.split(" ").includes(String(step)));
      node.classList.toggle("is-selected", node.dataset.node === selected);
      const item = info[node.dataset.node];
      node.setAttribute("aria-label", item[language === "en" ? 0 : 1]);
      node.setAttribute("aria-pressed", String(node.dataset.node === selected));
    });
    const item = info[selected];
    document.getElementById("selection-title").textContent = item[language === "en" ? 0 : 1];
    document.getElementById("selection-description").textContent = item[language === "en" ? 2 : 3];
    document.getElementById("selection-source").textContent = item[4];
    for (const format of ["svg","pdf","png"]) document.getElementById(`download-${format}`).href = `proof-search${language === "zh" ? ".zh" : ""}.${format}`;
  }

  function setStep(value) {
    step = value;
    selected = ["goal","wd","square","add","lookup","proof"][step];
    render();
  }
  for (let index=0;index<6;index++) {
    const button = document.createElement("button");
    button.type = "button";
    button.addEventListener("click", () => { stop();setStep(index); });
    track.appendChild(button);
  }
  document.querySelectorAll(".proof-figure").forEach(svg => svg.setAttribute("role", "group"));
  document.querySelectorAll(".node").forEach(node => {
    node.setAttribute("role", "button");
    node.setAttribute("tabindex", "0");
    const select = () => { stop();selected = node.dataset.node;render(); };
    node.addEventListener("click", select);
    node.addEventListener("keydown", event => { if(event.key === "Enter" || event.key === " "){event.preventDefault();select();} });
  });
  previous.addEventListener("click", () => { stop();if(step>0)setStep(step-1); });
  next.addEventListener("click", () => { stop();if(step<5)setStep(step+1); });
  play.addEventListener("click", () => {
    if(timer){stop();return;}
    if(step === 5)setStep(0);
    timer = setInterval(() => { if(step<5)setStep(step+1);if(step === 5)stop(); }, 2800);
    play.setAttribute("aria-pressed", "true");
    render();
  });
  for (const lang of ["en","zh"]) document.getElementById(`language-${lang}`).addEventListener("click", () => { language = lang;render(); });
  document.addEventListener("visibilitychange", () => { if(document.hidden)stop(); });
  document.getElementById("verification-summary").textContent = JSON.stringify(evidence,null,2);
  render();
})();
