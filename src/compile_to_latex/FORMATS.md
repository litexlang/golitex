# LaTeX formats by AST type

Every current leaf type has a format below. Mathematical precedence, domains, dimensions and logical scope belong to the compiler, not CSS. Bracketed dimension subscripts `[m,n]` retain explicit source size operands; they do not denote matrix entries. Entry access uses application. These are parse-only presentations, not verification certificates.

## Statements

The table describes top-level presentation. Inside a proof, all nested statements inherit inline flow: headings and branch labels run into the prose, field lists become inline field/type pairs, and formulas remain inline with their full mathematical content. Proof bodies have one paragraph and wrap naturally.

| AST leaf | Layout | Source fixture |
| --- | --- | --- |
| `Fact` | Relation/conjunction/quantifier-specific mathematics; top-level long calculations aligned; proof facts inline. | `examples/test_statements/fact.lit` |
| `Trust.TrustStmt` | Explicit trust heading; assumption paragraph with all supplied facts. | `examples/test_statements/trust_stmt.lit` |
| `Trust.TrustHaveStmt` | Explicit trust heading; typed bindings and their assumed conditions. | `examples/test_statements/trust_have_stmt.lit` |
| `Definition.DefineObj.LetObjStmt` | Let sentence with a named equality; expression precedence preserved. | `examples/test_statements/let_obj_stmt.lit` |
| `Definition.DefineObj.HaveObjInNonemptySetStmt` | Let sentence listing all bindings with their carriers. | `examples/test_statements/have_obj_in_nonempty_set_stmt.lit` |
| `Definition.DefineObj.HaveObjEqualStmt` | Typed bindings followed by their corresponding defining equalities. | `examples/test_statements/have_obj_equal_stmt.lit` |
| `Definition.DefineObj.HaveObjByExistFactsStmt` | Typed existential choice followed by its full condition conjunction. | `examples/test_statements/have_obj_by_exist_facts_stmt.lit` |
| `Definition.DefineObj.ObtainObjFromExistFact` | Choose witness names from the complete existential formula. | `examples/test_statements/obtain_obj_from_exist_fact.lit` |
| `Definition.DefineObj.ObtainObjFromAtomicFact` | Choose witness names from the named predicate instance. | `examples/test_statements/obtain_obj_from_atomic_fact.lit` |
| `Definition.DefineObj.HaveByPreimageStmt` | Choose named preimages from the original image-membership fact. | `examples/test_statements/have_by_preimage_stmt.lit` |
| `Definition.DefineObj.HaveByReplacementAxiomStmt` | Replacement construction names the result, predicate and source set. | `examples/test_statements/have_by_replacement_axiom_stmt.lit` |
| `Definition.HaveFnEqualStmt` | Definition heading; typed function signature; displayed defining equation. | `examples/test_statements/have_fn_equal_stmt.lit` |
| `Definition.HaveFnEqualCaseByCaseStmt` | Definition heading and signature; piecewise cases array with every condition. | `examples/test_statements/have_fn_equal_case_by_case_stmt.lit` |
| `Definition.HaveFnByInducStmt` | Definition heading, signature and measure/base; nested labelled recursive branches. | `examples/test_statements/have_fn_by_induc_stmt.lit` |
| `Definition.HaveFnByForallExistUniqueStmt` | Definition heading; name linked to the full quantified unique-existence specification. | `examples/test_statements/have_fn_by_forall_exist_unique_stmt.lit` |
| `Definition.DefPropStmt` | Definition heading; typed universal parameters above an iff and conjunctive clauses. | `examples/test_statements/def_prop_stmt.lit` |
| `Definition.DefAbstractPropStmt` | Abstract-predicate heading and arity-preserving signature; no invented body. | `examples/test_statements/def_abstract_prop_stmt.lit` |
| `Definition.DefTemplateStmt` | Template heading and typed parameters/guards; scoped rendering of the actual inner definition. | `examples/test_statements/def_template_stmt.lit` |
| `Definition.DefStructStmt` | Structure heading and parameters; labelled field/type list; displayed laws. | `examples/test_statements/def_struct_stmt.lit` |
| `Definition.DefAlgoByCasesStmt` | Algorithm heading and function signature; piecewise executable equations. | `examples/test_statements/def_algo_by_cases_stmt.lit` |
| `Definition.DefAlgoByInducStmt` | Algorithm heading, signature, measure/base and nested recursive branches. | `examples/test_statements/def_algo_by_induc_stmt.lit` |
| `Definition.DefThmStmt` | Theorem heading, full goal; one source proof with a closing square when present. | `examples/test_statements/def_thm_stmt.lit` |
| `Definition.AxiomStmt` | Axiom heading and full quantified assertion; no fabricated proof. | `examples/test_statements/axiom_stmt.lit` |
| `Definition.DefStrategyStmt` | Strategy heading, complete goal, source proof and closing marker. | `examples/test_statements/def_strategy_stmt.lit` |
| `ReleaseAndExpand.ReleaseThmStmt` | Theorem-application paragraph with exact theorem and argument groups. | `examples/test_statements/release_thm_stmt.lit` |
| `ReleaseAndExpand.ReleaseStructDefStmt` | Structure-opening paragraph identifying the original object. | `examples/test_statements/release_struct_def_stmt.lit` |
| `ReleaseAndExpand.ReleaseObjDefStmt` | Definition-opening paragraph identifying the original qualified name. | `examples/test_statements/release_obj_def_stmt.lit` |
| `ReleaseAndExpand.ReleaseCartDefStmt` | Definition-opening paragraph displaying the complete Cartesian product. | `examples/test_statements/release_cart_def_stmt.lit` |
| `ReleaseAndExpand.ReleaseTupleDefStmt` | Definition-opening paragraph displaying the original tuple expression. | `examples/test_statements/release_tuple_def_stmt.lit` |
| `ReleaseAndExpand.ExpandRangeStmt` | Range-expansion paragraph; integer membership keeps open/closed end points. | `examples/test_statements/expand_range_stmt.lit` |
| `ReleaseAndExpand.ReleaseZornLemmaStmt` | Zorn application with set and all three named predicates; scoped hypothesis-checking proof. | `examples/test_statements/release_zorn_lemma_stmt.lit` |
| `ReleaseAndExpand.ReleaseAxiomOfChoiceStmt` | Choice application with the family; scoped hypothesis-checking proof. | `examples/test_statements/release_axiom_of_choice_stmt.lit` |
| `ReleaseAndExpand.ReleaseRegularityAxiomStmt` | Regularity-application paragraph naming the original set. | `examples/test_statements/release_regularity_axiom_stmt.lit` |
| `By.ByCasesStmt` | Continuous goal, labelled cases, assumptions, proof steps and common conclusion in one paragraph. | `examples/stmt_nodes/compile_to_latex/structured_proof_layout.lit` |
| `By.ByContraStmt` | Run-in contradiction label, goal, contrary assumption, derivation and explicit conclusion in one paragraph. | `examples/stmt_nodes/compile_to_latex/structured_proof_layout.lit` |
| `By.ByEnumerateFiniteSetStmt` | Finite-enumeration goal followed by inline proof steps. | `examples/test_statements/by_enumerate_finite_set_stmt.lit` |
| `By.ByInducStmt` | Inline goal and induction/base introduction; run-in base/step labels and common proof steps. | `examples/test_statements/by_induc_stmt.lit` |
| `By.ByStrongInducStmt` | Inline goal and strong-induction/base introduction; run-in base/step labels. | `examples/test_statements/by_strong_induc_stmt.lit` |
| `By.ByForStmt` | Finite-iteration goal followed by inline proof steps. | `examples/test_statements/by_for_stmt.lit` |
| `By.ByExtensionStmt` | Set-extensionality target equality followed by a scoped proof body. | `examples/test_statements/by_extension_stmt.lit` |
| `By.ByFnExtensionStmt` | Function-extensionality target equality followed by a scoped proof body. | `examples/test_statements/by_fn_extension_stmt.lit` |
| `By.ByDefStmt` | Definition-unfolding paragraph showing the exact predicate instance. | `examples/test_statements/by_def_stmt.lit` |
| `By.ByThmStmt` | Theorem citation paragraph with the call and the selected conclusion. | `examples/test_statements/by_thm_stmt.lit` |
| `Register.RegisterTransitivePropStmt` | Transitivity-registration paragraph with the complete universal law. | `examples/test_statements/register_transitive_prop_stmt.lit` |
| `Register.RegisterSymmetricPropStmt` | Symmetry-registration paragraph with the complete universal law. | `examples/test_statements/register_symmetric_prop_stmt.lit` |
| `Register.RegisterReflexivePropStmt` | Reflexivity-registration paragraph with the complete universal law. | `examples/test_statements/register_reflexive_prop_stmt.lit` |
| `Witness.WitnessExistFact` | Witness values, existential goal and inline proof steps. | `examples/test_statements/witness_exist_fact.lit` |
| `Witness.WitnessAtomicFact` | Witness values, named atomic goal and inline proof steps. | `examples/test_statements/witness_atomic_fact.lit` |
| `Witness.WitnessNonemptySet` | Witness, nonempty-set goal and inline proof steps. | `examples/test_statements/witness_nonempty_set.lit` |
| `ProofBlock.ClaimStmt` | Claim heading and full assertion; one continuous proof paragraph with an inline closing square. | `examples/stmt_nodes/compile_to_latex/structured_proof_layout.lit` |
| `ProofBlock.SketchStmt` | Explicit run-in sketch label and inline local statements; no proof-completion claim. | `examples/test_statements/sketch_stmt.lit` |
| `Command.EvalStmt` | Evaluation-request paragraph; the expression is shown without an invented computed result. | `examples/test_statements/eval_stmt.lit` |

## Objects

| AST leaf | Litex expression | Mathematical template |
| --- | --- | --- |
| `MatrixOperator.Determinant` | `det(A,n)` | `\det_n(A)` |
| `MatrixOperator.ZeroMatrix` | `zero_matrix(m,n)` | `0_{m\times n}` |
| `MatrixOperator.IdentityMatrix` | `identity_matrix(n)` | `I_n` |
| `MatrixOperator.Transpose` | `transpose(A,m,n)` | `(A^{\mathsf T})_{[m,n]}` |
| `MatrixOperator.ConjugateTranspose` | `conjugate_transpose(A,m,n)` | `(A^{\mathsf H})_{[m,n]}` |
| `MatrixOperator.Trace` | `trace(A,n)` | `\operatorname{tr}_n(A)` |
| `MatrixOperator.Add` | `matrix_add(A,B,m,n)` | `(A+B)_{[m,n]}` |
| `MatrixOperator.Subtract` | `matrix_sub(A,B,m,n)` | `(A-B)_{[m,n]}` |
| `MatrixOperator.Scale` | `matrix_scale(c,A,m,n)` | `(cA)_{[m,n]}` |
| `MatrixOperator.Multiply` | `matrix_mul(A,B,m,k,n)` | `(AB)_{[m,k,n]}` |
| `MatrixOperator.Apply` | `matrix_apply(A,v,m,n)` | `(Av)_{[m,n]}` |
| `MatrixOperator.Power` | `matrix_power(A,n,k)` | `(A^k)_{[n]}` |
| `MatrixOperator.Inverse` | `matrix_inv(A,n)` | `(A^{-1})_{[n]}` |
| `MatrixOperator.Rank` | `matrix_rank(A,m,n)` | `\operatorname{rank}_{[m,n]}(A)` |
| `MatrixOperator.Minor` | `matrix_minor(A,n,k,j)` | `A_{\widehat k,\widehat j}^{[n]}` |
| `MatrixOperator.Cofactor` | `matrix_cofactor(A,n,k,j)` | `\operatorname{cof}_{k,j}^{[n]}(A)` |
| `MatrixOperator.Adjugate` | `matrix_adjugate(A,n)` | `\operatorname{adj}_n(A)` |
| `MatrixOperator.Diagonal` | `diagonal_matrix(v,n)` | `\operatorname{diag}_n(v)` |
| `MatrixOperator.OuterProduct` | `outer_product(u,v,m,n)` | `(uv^{\mathsf T})_{[m,n]}` |
| `MatrixOperator.InnerProduct` | `inner_product(u,v,n)` | `\langle u,v\rangle_{[n]}` |
| `MatrixOperator.EuclideanNorm` | `euclidean_norm(v,n)` | `\lVert v\rVert_{2,[n]}` |
| `MatrixOperator.FrobeniusNorm` | `frobenius_norm(A,m,n)` | `\lVert A\rVert_{\mathrm F,[m,n]}` |
| `BoundOperator.Supremum` | `sup(S)` | `\sup(S)` |
| `BoundOperator.Infimum` | `inf(S)` | `\inf(S)` |
| `IntegralOperator.Riemann` | `integral(f,a,b)` | `\int_a^b f(\xi)\,\mathrm d\xi` |
| `DerivativeOperator.Partial` | `partial_derivative(f,a,n,j)` | `(\frac{\partial f}{\partial x_j}(a))_{[n]}` |
| `DerivativeOperator.ScalarDifferential` | `scalar_differential(f,a,n)` | `(Df(a))_{[n]}` |
| `DerivativeOperator.TotalDifferential` | `differential(f,a,m,n)` | `(Df(a))_{[m,n]}` |
| `DerivativeOperator.Gradient` | `gradient_at(f,a,n)` | `(\nabla f(a))_{[n]}` |
| `DerivativeOperator.Jacobian` | `jacobian(f,a,m,n)` | `(J_f(a))_{[m,n]}` |
| `DerivativeOperator.Hessian` | `hessian(f,a,n)` | `(H_f(a))_{[n]}` |
| `DerivativeOperator.Divergence` | `divergence(f,a,n)` | `(\nabla\cdot f(a))_{[n]}` |
| `DerivativeOperator.Curl` | `curl(f,a)` | `\nabla\times f(a)` |
| `DerivativeOperator.Laplacian` | `laplacian(f,a,n)` | `(\Delta f(a))_{[n]}` |
| `DerivativeOperator.AtPoint` | `derivative(f,a)` | `f^{\prime}(a)` |
| `Identifier.Plain` | `x` | `x` |
| `Identifier.WithExportFileId` | `alpha::x` | `\mathit{alpha::x}` |
| `Identifier.WithModAndExportFileId` | `dep::beta::x` | `\mathit{dep::beta::x}` |
| `FnObj` | `f(x)(y)` | `f(x)(y)` |
| `Literal.Number` | `1.25` | `1.25` |
| `Literal.ImaginaryUnit` | `i` | `\mathrm{i}` |
| `Literal.EulerNumber` | `e` | `\mathrm{e}` |
| `Literal.Pi` | `pi` | `\pi` |
| `StandardSet.NPos` | `N+` | `\mathbb{N}_{>0}` |
| `StandardSet.N` | `N` | `\mathbb{N}` |
| `StandardSet.Q` | `Q` | `\mathbb{Q}` |
| `StandardSet.Z` | `Z` | `\mathbb{Z}` |
| `StandardSet.R` | `R` | `\mathbb{R}` |
| `StandardSet.C` | `C` | `\mathbb{C}` |
| `StandardSet.QPos` | `Q+` | `\mathbb{Q}_{>0}` |
| `StandardSet.RPos` | `R+` | `\mathbb{R}_{>0}` |
| `StandardSet.QNeg` | `Q-` | `\mathbb{Q}_{<0}` |
| `StandardSet.ZNeg` | `Z-` | `\mathbb{Z}_{<0}` |
| `StandardSet.RNeg` | `R-` | `\mathbb{R}_{<0}` |
| `StandardSet.QStar` | `Q*` | `\mathbb{Q}_{\ne 0}` |
| `StandardSet.ZStar` | `Z*` | `\mathbb{Z}_{\ne 0}` |
| `StandardSet.RStar` | `R*` | `\mathbb{R}_{\ne 0}` |
| `StandardSet.CStar` | `C*` | `\mathbb{C}_{\ne 0}` |
| `ArithmeticOperator.Add` | `a+b` | `a+b` |
| `ArithmeticOperator.Sub` | `a-b` | `a-b` |
| `ArithmeticOperator.Neg` | `-a` | `-a` |
| `ArithmeticOperator.Mul` | `a*b` | `a\cdot b` |
| `ArithmeticOperator.Div` | `a/b` | `\frac{a}{b}` |
| `ArithmeticOperator.Pow` | `a^b` | `a^b` |
| `ArithmeticOperator.Abs` | `abs(a)` | `\lvert a\rvert` |
| `ArithmeticOperator.Min` | `min(a,b)` | `\min(a,b)` |
| `ArithmeticOperator.Max` | `max(a,b)` | `\max(a,b)` |
| `ArithmeticOperator.Floor` | `floor(a)` | `\lfloor a\rfloor` |
| `ArithmeticOperator.Ceil` | `ceil(a)` | `\lceil a\rceil` |
| `ArithmeticOperator.Sign` | `sign(a)` | `\operatorname{sgn}(a)` |
| `IntegerOperator.Mod` | `a % b` | `a\bmod b` |
| `IntegerOperator.Quot` | `quot(a,b)` | `\operatorname{quot}(a,b)` |
| `IntegerOperator.Gcd` | `gcd(a,b)` | `\gcd(a,b)` |
| `IntegerOperator.Lcm` | `lcm(a,b)` | `\operatorname{lcm}(a,b)` |
| `IntegerOperator.Factorial` | `factorial(n)` | `n!` |
| `TrigOperator.Sin` | `sin(x)` | `\operatorname{sin}(x)` |
| `TrigOperator.Cos` | `cos(x)` | `\operatorname{cos}(x)` |
| `TrigOperator.Tan` | `tan(x)` | `\operatorname{tan}(x)` |
| `TrigOperator.Cot` | `cot(x)` | `\operatorname{cot}(x)` |
| `TrigOperator.Sec` | `sec(x)` | `\operatorname{sec}(x)` |
| `TrigOperator.Csc` | `csc(x)` | `\operatorname{csc}(x)` |
| `TrigOperator.Arcsin` | `arcsin(x)` | `\operatorname{arcsin}(x)` |
| `TrigOperator.Arccos` | `arccos(x)` | `\operatorname{arccos}(x)` |
| `TrigOperator.Arctan` | `arctan(x)` | `\operatorname{arctan}(x)` |
| `TrigOperator.Arccot` | `arccot(x)` | `\operatorname{arccot}(x)` |
| `HyperbolicOperator.Sinh` | `sinh(x)` | `\operatorname{sinh}(x)` |
| `HyperbolicOperator.Cosh` | `cosh(x)` | `\operatorname{cosh}(x)` |
| `HyperbolicOperator.Tanh` | `tanh(x)` | `\operatorname{tanh}(x)` |
| `HyperbolicOperator.Coth` | `coth(x)` | `\operatorname{coth}(x)` |
| `HyperbolicOperator.Sech` | `sech(x)` | `\operatorname{sech}(x)` |
| `HyperbolicOperator.Csch` | `csch(x)` | `\operatorname{csch}(x)` |
| `LimitOperator.MultivariableScalar` | `lim_multi_at(f,a,n)` | `(\lim_{\xi\to a}f(\xi))_{[n]}` |
| `LimitOperator.MultivariableVector` | `lim_vector_at(f,a,m,n)` | `(\lim_{\xi\to a}f(\xi))_{[m,n]}` |
| `LimitOperator.Sequence` | `lim(a)` | `\lim_{n\to\infty}a(n)` |
| `LimitOperator.SequenceLimsup` | `limsup(a)` | `\limsup_{n\to\infty}a(n)` |
| `LimitOperator.SequenceLiminf` | `liminf(a)` | `\liminf_{n\to\infty}a(n)` |
| `LimitOperator.Function` | `fn_lim(f,a)` | `\lim_{x\to a,\ x\in\operatorname{dom}(f)} f(x)` |
| `ExpLogOperator.Exp` | `exp(x)` | `\mathrm{e}^{x}` |
| `ExpLogOperator.Ln` | `ln(x)` | `\ln(x)` |
| `ExpLogOperator.Log` | `log(b,x)` | `\log_b(x)` |
| `ExpLogOperator.Sqrt` | `sqrt(x)` | `\sqrt{x}` |
| `ComplexOperator.Conjugate` | `conj(z)` | `\overline{z}` |
| `ComplexOperator.RealPart` | `re(z)` | `\operatorname{Re}(z)` |
| `ComplexOperator.ImaginaryPart` | `img(z)` | `\operatorname{Im}(z)` |
| `ComplexOperator.ComplexAbs` | `C_abs(z)` | `\lvert z\rvert` |
| `SetOperator.Union` | `union(A,B)` | `A\cup B` |
| `SetOperator.Intersect` | `intersect(A,B)` | `A\cap B` |
| `SetOperator.SetMinus` | `set_minus(A,B)` | `A\setminus B` |
| `SetOperator.SymmetricDifference` | `set_diff(A,B)` | `A\triangle B` |
| `SetOperator.FamilyUnion` | `family_union(F)` | `\bigcup F` |
| `SetOperator.FamilyIntersect` | `family_intersect(F)` | `\bigcap F` |
| `SetOperator.IndexUnion` | `index_union(I,X,F)` | `\{x\in X\mid\exists i\in I:x\in F(i)\}` |
| `SetOperator.IndexIntersect` | `index_intersect(I,X,F)` | `\{x\in X\mid\forall i\in I:x\in F(i)\}` |
| `SetOperator.PowerSet` | `power_set(A)` | `\mathcal P(A)` |
| `SetOperator.IndexCart` | `index_cart(I,S,F)` | `\operatorname{IndexCart}(I,S,F)` |
| `SetFormer.ListSet` | `{a,b}` | `\{a,b\}` |
| `SetFormer.SetBuilder` | `{t R: t>0}` | `\{t\in\mathbb R\mid t>0\}` |
| `SetFormer.Range` | `range(a,b)` | `\{i\in\mathbb Z\mid a\le i<b\}` |
| `SetFormer.ClosedRange` | `closed_range(a,b)` | `\{i\in\mathbb Z\mid a\le i\le b\}` |
| `SetFormer.FiniteSeqSet` | `finite_seq(S,n)` | `S^{\{i\in\mathbb N_{>0}\mid i\le n\}}` |
| `SetFormer.MatrixSet` | `matrix(S,m,n)` | `S^{m\times n}` |
| `SetFormer.SeqSet` | `seq(S)` | `S^{\mathbb N_{>0}}` |
| `SetFormer.OneSideInfinityIntervalObj.LowerOpen` | `'(a,)` | `(a,+\infty)` |
| `SetFormer.OneSideInfinityIntervalObj.LowerClosed` | `'[a,)` | `[a,+\infty)` |
| `SetFormer.OneSideInfinityIntervalObj.UpperOpen` | `'(,b)` | `(-\infty,b)` |
| `SetFormer.OneSideInfinityIntervalObj.UpperClosed` | `'(,b]` | `(-\infty,b]` |
| `SetFormer.IntervalObj.LeftOpenRightOpen` | `'(a,b)` | `(a,b)` |
| `SetFormer.IntervalObj.LeftOpenRightClosed` | `'(a,b]` | `(a,b]` |
| `SetFormer.IntervalObj.LeftClosedRightOpen` | `'[a,b)` | `[a,b)` |
| `SetFormer.IntervalObj.LeftClosedRightClosed` | `'[a,b]` | `[a,b]` |
| `ProductShape.Cart` | `cart(A,B)` | `A\times B` |
| `ProductShape.Tuple` | `(a,b)` | `(a,b)` |
| `FunctionSpace.FnSet` | `fn(t R) R` | `\mathbb R\to\mathbb R` |
| `FunctionSpace.AnonymousFn` | `fn(t R) R {t+1}` | `[\mathbb R\to\mathbb R;\ t\mapsto t+1]` |
| `FunctionSpace.Composition` | `compose(f,g)` | `f\circ g` |
| `FunctionSpace.FnRange` | `fn_range(f)` | `\operatorname{range}(f)` |
| `FunctionSpace.Preimage` | `preimage(f,y)` | `f^{-1}[\{y\}]` |
| `FunctionSpace.PreimageSet` | `preimage_set(f,S)` | `f^{-1}[S]` |
| `IteratedOperator.Sum` | `sum(a,b,f)` | `\sum_{i=a}^{b}f(i)` |
| `IteratedOperator.SumOfFiniteSet` | `finite_set_sum(S,f)` | `\sum_{i\in S}f(i)` |
| `IteratedOperator.Product` | `product(a,b,f)` | `\prod_{i=a}^{b}f(i)` |
| `IteratedOperator.ProductOfFiniteSet` | `finite_set_product(S,f)` | `\prod_{i\in S}f(i)` |
| `IteratedOperator.Reduce` | `reduce(a,b,f,op,s)` | `\operatorname{reduce}(a,b,f,op,s)` |
| `IteratedOperator.FiniteSetReduce` | `finite_set_reduce(S,f,op,s)` | `\operatorname{finiteReduce}(S,f,op,s)` |
| `FiniteSetStat.FiniteSetSize` | `finite_set_size(S)` | `\lvert S\rvert` |
| `FiniteSetStat.FiniteSetMax` | `finite_set_max(S)` | `\max(S)` |
| `FiniteSetStat.FiniteSetMin` | `finite_set_min(S)` | `\min(S)` |
| `StructAndFieldAccessObj.StructObj` | `&Point<R>` | `\mathit{Point}\langle\mathbb R\rangle` |
| `StructAndFieldAccessObj.FieldAccess` | `p.x.y` | `p.x.y` |
| `InstantiatedTemplateObj` | `\carrier<R>` | `\mathit{carrier}\langle\mathbb R\rangle` |

## Application heads and limit directions

| AST helper | Source | Format |
| --- | --- | --- |
| `FnObjHead.Identifier` | `let specimen = f(x)` | Applied head preserves its own grouping, followed by each curried argument group. |
| `FnObjHead.AnonymousFnLiteral` | `let specimen = fn(t R) R {t}(a)` | Applied head preserves its own grouping, followed by each curried argument group. |
| `FnObjHead.FieldAccess` | `let specimen = p.f(x)` | Applied head preserves its own grouping, followed by each curried argument group. |
| `FnObjHead.InstantiatedTemplateObj` | `let specimen = \carrier<R>(x)` | Applied head preserves its own grouping, followed by each curried argument group. |
| `FnObjHead.Object` | `let specimen = compose(f,g)(x)` | Applied head preserves its own grouping, followed by each curried argument group. |
| `LimitApproach.AtPoint` | `let specimen = fn_lim(f,a)` | Limit direction and function-domain restriction remain explicit; generated variable avoids source-name collisions. |
| `LimitApproach.FromLeft` | `let specimen = lim_left(f,a)` | Limit direction and function-domain restriction remain explicit; generated variable avoids source-name collisions. |
| `LimitApproach.FromRight` | `let specimen = lim_right(f,a)` | Limit direction and function-domain restriction remain explicit; generated variable avoids source-name collisions. |
| `LimitApproach.AtPositiveInfinity` | `let specimen = lim_pos_inf(f)` | Limit direction and function-domain restriction remain explicit; generated variable avoids source-name collisions. |
| `LimitApproach.AtNegativeInfinity` | `let specimen = lim_neg_inf(f)` | Limit direction and function-domain restriction remain explicit; generated variable avoids source-name collisions. |

The machine catalog is maintained in `tests/fixtures/compile_to_latex/format_catalog.json`. Tests parse each source, confirm the actual AST type, and render it through the production compiler. Exhaustive Rust matches and catalog set comparisons detect omissions. The source catalog includes trust/sketch/evaluation requests explicitly; rendering them does not assert their truth.


## Logical fact shapes

| Fact variant | Format |
| --- | --- |
| `AtomicFact` | Atomic relation or named predicate with all arguments. |
| `ExistFact` | Existential binder followed by its full condition. |
| `ExistUniqueFact` | Unique-existence binder and its complete condition. |
| `NotExistFact` | Negated existential with preserved binder scope. |
| `OrFact` | Grouped disjuncts joined by logical disjunction. |
| `AndFact` | Conjunctive clauses displayed in aligned rows. |
| `ChainFact` | Aligned calculation preserving each adjacent relation. |
| `ForallFact` | Typed universal statement; guards and all conclusions retained. |
| `ForallFactWithIff` | Typed universal binder followed by a grouped equivalence. |
| `NotForall` | Negation scopes over the entire quantified assertion. |
