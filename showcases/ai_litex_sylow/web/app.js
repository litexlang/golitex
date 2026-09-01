(() => {
  "use strict";

  const data = window.SYLOW_SHOWCASE;
  if (!data) throw new Error("lesson-data.js did not define window.SYLOW_SHOWCASE");

  const elements = {
    heroSubtitle: document.querySelector("#hero-subtitle"),
    scopeNote: document.querySelector("#scope-note"),
    lensDescription: document.querySelector("#lens-description"),
    lensButtons: [...document.querySelectorAll("[data-lens]")],
    stepCount: document.querySelector("#step-count"),
    progressFill: document.querySelector("#progress-fill"),
    stepNav: document.querySelector("#step-nav"),
    stage: document.querySelector("#lesson-stage"),
    stepPhase: document.querySelector("#step-phase"),
    stepTitle: document.querySelector("#step-title"),
    stepStatus: document.querySelector("#step-status"),
    mathCopy: document.querySelector("#math-copy"),
    engineeringCopy: document.querySelector("#engineering-copy"),
    code: document.querySelector("#step-code"),
    evidence: document.querySelector("#step-evidence"),
    codeTab: document.querySelector("#code-tab"),
    evidenceTab: document.querySelector("#evidence-tab"),
    codePanel: document.querySelector("#code-panel"),
    evidencePanel: document.querySelector("#evidence-panel"),
    journalLink: document.querySelector("#journal-link"),
    previous: document.querySelector("#previous-step"),
    next: document.querySelector("#next-step"),
    currentNumber: document.querySelector("#current-step-number"),
    boundary: document.querySelector("#boundary-columns"),
    buildMeta: document.querySelector("#build-meta")
  };

  let currentIndex = Math.max(0, data.steps.findIndex((step) => `#${step.id}` === window.location.hash));
  let currentLens = "mathematics";
  let artifactView = "code";

  function make(tag, className, text) {
    const node = document.createElement(tag);
    if (className) node.className = className;
    if (text !== undefined) node.textContent = text;
    return node;
  }

  function renderNavigation() {
    elements.stepNav.replaceChildren();
    data.steps.forEach((step, index) => {
      const button = make("button", "step-link", step.title);
      button.type = "button";
      button.dataset.number = String(index + 1).padStart(2, "0");
      button.setAttribute("aria-current", index === currentIndex ? "step" : "false");
      button.addEventListener("click", () => selectStep(index, true));
      elements.stepNav.append(button);
    });
  }

  function renderStatus(label) {
    elements.stepStatus.textContent = label;
    elements.stepStatus.className = "status-pill";
    if (/rolled back/i.test(label)) elements.stepStatus.classList.add("rollback");
    else if (/goal|cited|written/i.test(label)) elements.stepStatus.classList.add("neutral");
  }

  function setArtifactView(view) {
    artifactView = view;
    const showCode = view === "code";
    elements.codeTab.setAttribute("aria-selected", String(showCode));
    elements.evidenceTab.setAttribute("aria-selected", String(!showCode));
    elements.codePanel.hidden = !showCode;
    elements.evidencePanel.hidden = showCode;
  }

  function renderStep() {
    const step = data.steps[currentIndex];
    elements.stepPhase.textContent = step.phase;
    elements.stepTitle.textContent = step.title;
    renderStatus(step.status_label);
    elements.mathCopy.textContent = step.mathematics;
    elements.engineeringCopy.textContent = step.engineering;
    elements.code.textContent = step.code;
    elements.evidence.textContent = JSON.stringify(step.evidence, null, 2);
    const normalStep = step.id === "normal_extension";
    const sylowStep = step.id === "sylow_final";
    elements.journalLink.href = step.journal ?? (normalStep ? "normal_subgroup_journal.json" : "proof_journal.json");
    elements.journalLink.textContent = sylowStep ? "open final Sylow journal ↗" : normalStep ? "open normal journal ↗" : "open source journal ↗";
    elements.previous.disabled = currentIndex === 0;
    elements.next.disabled = currentIndex === data.steps.length - 1;
    elements.next.textContent = currentIndex === data.steps.length - 1 ? "Proof complete ✓" : "Next step →";
    elements.currentNumber.textContent = `${String(currentIndex + 1).padStart(2, "0")} / ${String(data.steps.length).padStart(2, "0")}`;
    elements.progressFill.style.width = `${((currentIndex + 1) / data.steps.length) * 100}%`;
    artifactView = /rolled back/i.test(step.status_label) ? "evidence" : "code";
    setArtifactView(artifactView);
    renderNavigation();
  }

  function selectStep(index, updateHash = false) {
    if (index < 0 || index >= data.steps.length) return;
    currentIndex = index;
    if (updateHash) history.replaceState(null, "", `#${data.steps[index].id}`);
    renderStep();
    elements.stage.focus({ preventScroll: true });
  }

  function selectLens(lens) {
    currentLens = lens;
    document.body.classList.toggle("lens-mathematics", lens === "mathematics");
    document.body.classList.toggle("lens-engineering", lens === "engineering");
    elements.lensButtons.forEach((button) => button.setAttribute("aria-pressed", String(button.dataset.lens === lens)));
    elements.lensDescription.textContent = data.audiences[lens].description;
  }

  function renderBoundary() {
    const groups = [
      ["Checked here", data.trust_boundary.checked_here],
      ["Outside this claim", data.trust_boundary.outside_claim]
    ];
    elements.boundary.replaceChildren(...groups.map(([title, items]) => {
      const card = make("section", "boundary-card");
      card.append(make("h3", "", title));
      const list = make("ul");
      items.forEach((item) => list.append(make("li", "", item)));
      card.append(list);
      return card;
    }));
  }

  elements.heroSubtitle.textContent = data.meta.one_sentence;
  elements.scopeNote.textContent = data.meta.scope_note;
  elements.stepCount.textContent = `${data.steps.length} steps`;
  elements.buildMeta.textContent = `${data.meta.binary} · ${data.meta.journal_id}`;
  elements.lensButtons.forEach((button) => button.addEventListener("click", () => selectLens(button.dataset.lens)));
  elements.codeTab.addEventListener("click", () => setArtifactView("code"));
  elements.evidenceTab.addEventListener("click", () => setArtifactView("evidence"));
  elements.previous.addEventListener("click", () => selectStep(currentIndex - 1, true));
  elements.next.addEventListener("click", () => selectStep(currentIndex + 1, true));

  window.addEventListener("keydown", (event) => {
    if (event.altKey || event.ctrlKey || event.metaKey || event.shiftKey) return;
    if (event.key === "ArrowLeft") selectStep(currentIndex - 1, true);
    if (event.key === "ArrowRight") selectStep(currentIndex + 1, true);
  });

  window.addEventListener("hashchange", () => {
    const index = data.steps.findIndex((step) => `#${step.id}` === window.location.hash);
    if (index >= 0 && index !== currentIndex) selectStep(index, false);
  });

  selectLens(currentLens);
  renderBoundary();
  renderStep();
})();
