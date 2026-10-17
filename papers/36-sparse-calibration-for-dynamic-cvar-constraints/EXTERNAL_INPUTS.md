# Paper 36 external inputs — exact contracts and scope

This document preserves the precise original external interfaces, use sites and narrative complexity boundaries. Source-specific mathematics remains in the production modules. Fresh aggregate compilation, full audit/replay and official Comparator have not run; in particular `CalibrationScan.lean` and `ComplexityEncoding.lean` lacked production artifacts at delivery. Historical owner statements are not fresh release validation.

## E1. Finite categorical method-of-types inequality

**Reference.** T. M. Cover and J. A. Thomas, *Elements of Information Theory*, second edition, Wiley, 2006, source reference [12], DOI [10.1002/047174882X](https://doi.org/10.1002/047174882X). Existing posterior record cites the method-of-types bound, without claiming a freshly verified numbered theorem.

**Exact quantifiers and hypotheses.** For every finite categorical space `S`, every probability vector `P : CVaR.Law S`, every integer `n>0`, and every real `Lambda>=0`, under the actual product law of `n` iid samples with common law `P`,

`Pr[ KL(empirical_n || P) > Lambda/n ] <= (n+1)^(card S) * exp(-Lambda)`.

KL has value infinity when empirical support is not dominated by `P`. No strict positivity of coordinates of `P`, positive minimum probability, independent prior coordinates, conjugate prior, identifiability or posterior concentration is assumed.

**Lean interface.** `RowTapes.ExternalCategoricalConcentration.methodTypes` quantifies exactly over `P n hn Lambda`; probability comparison uses `ENNReal.ofReal` and extended-real KL. `RowTapes.iidLaw` and `empirical` are actual finite masses, not abstract “good events”.

**Use sites.** `RowTapes` arbitrary-prior mixture, prefix bounds; `Statistical.PosteriorSystem.current_kl_failure_probability`, `current_kl_failure_probability_budget`, `lemma_5_5`, `theorem_5_6`; corresponding `Statistical.PosteriorSystem.stage_lemma_5_5`, `stage_theorem_5_6`; downstream `Main.modelRisk_bound` and main/certified performance. Adaptive source tapes and raw conditional sampling laws are not part of this external theorem.

## E2. Weissman categorical total-variation inequality

**Reference.** T. Weissman, E. Ordentlich, G. Seroussi, S. Verdú and M. J. Weinberger, *Inequalities for the L1 Deviation of the Empirical Distribution*, HP Labs Technical Report HPL-2003-97R1, 2003, source reference [34]. Existing record preserves report identity and does not claim a newly checked online theorem number.

**Exact quantifiers and hypotheses.** For every finite categorical `S`, every law `P`, integer `n>0`, and `L>=0`, for actual iid samples from `P`,

`Pr[ TV(empirical_n,P) > sqrt(L/(2*n)) ] <= (2^(card S)-2)*exp(-L)`.

Here `TV(P,Q)=(1/2)*sum_s |P(s)-Q(s)|`. Degenerate zero coordinates are permitted. The singleton case has zero failure probability; the stated prefactor is retained literally.

**Lean interface.** `RowTapes.ExternalCategoricalConcentration.weissman` with the same explicit product law and actual empirical distribution.

**Use sites.** `RowTapes.weissman_arbitrary_prior`, fixed-prefix/current-count transfer; `Statistical.PosteriorSystem.current_tv_failure_probability`, `reward_expectation_bound_raw`, `lemma_5_8`; `Main.modelReward_bound`. The source-specific reward simulation, ordinary Bellman recursion, count charging, Jensen and constant 8 are own proofs.

## E3. Labelled comparison sorting with a uniform count bound

**References.** D. E. Knuth, *The Art of Computer Programming*, volume 3, second edition, 1998, Section 5.2.4 (merge sorting), or Section 5.2.1 for the sufficient quadratic insertion-sort variant. Published concrete algorithm: C. Bron, “Algorithm 426: Merge sort algorithm [M1]”, *Communications of the ACM* 15(5), 1972, pp. 357–358, DOI [10.1145/355602.361317](https://doi.org/10.1145/355602.361317), [publisher/institution record](https://research.tue.nl/en/publications/algorithm-426-merge-sort-algorithm-m1/). Existing supplementary bound record: M. A. Suchenek, *Elementary Yet Precise Worst-case Analysis of MergeSort*, [arXiv:1702.08443](https://arxiv.org/abs/1702.08443).

**Exact quantifiers and hypotheses.** There exists one deterministic algorithm such that for every `n>=0` and real labelled key vector `g : Fin n -> R`, including repeated keys, it returns a permutation `e : Equiv.Perm (Fin n)` whose reordered keys are antitone. Under unit real-key comparison counting it has a uniform budget `T(n)=n*ceil(log2(max(1,n)))`, with `T(0)=0`; a uniform constant multiple permits other scalar conventions. In particular there is a uniform constant `K` giving at most `K*n*n` operations. The uniformity is across all key vectors, not an instance-specific bound.

**Lean interface.** `sorter : (g : Fin n -> R) -> CalibrationScan.SortedOrder n g` with permutation, antitone order and an explicit `operations : Nat`. Refined theorems take `forall g, (sorter g).operations <= T`; coarse theorems take the uniform `<=K*n*n` contract.

**Use sites.** `CalibrationScan.evaluateDP` sorts one continuation-value vector per stage, reuses its labelled state ordering for every state-action row, materializes each scalar action value once, and scans minima. `evaluateDP_cost_budget` proves

`H*(T + S*A*(5*S+1) + S*(A-1))`.

Thus generic merge sorting yields the source `O(H[S log S + A S²])`. `evaluateDP_cost` / `proposition4_1_actions` give `H*(K+7)*A*S²`. The full greedy CVaR scan, optimizer certificate, sorted shift invariance, row law reindexing, exact value, minimizing action lookup and deterministic policy optimality are own.

**Cost model.** Exact-real scalar comparison/add/sub/mul/div are unit operations, as in the source. Array indexing, finite index bookkeeping and ghost counters are outside this scalar-operation cost. No bit-time or arbitrary-real runtime guarantee is inferred.

## E4. Positive binary Subset Sum NP-completeness

**Reference.** R. M. Karp, “Reducibility Among Combinatorial Problems”, *Complexity of Computer Computations*, 1972, pp. 85–103, DOI [10.1007/978-1-4684-2001-2_9](https://doi.org/10.1007/978-1-4684-2001-2_9). Existing complexity record identifies complete-problem list problem 18 KNAPSACK and the positive-integer convention in Appendix I; [primary scan](https://www.cs.umd.edu/~gasarch/BLOGPAPERS/Karp.pdf).

**Exact quantifiers.** The language of all finite binary lists of positive integers `w_1,...,w_n` and positive integer `B` for which some subset has sum exactly `B` is NP-complete under deterministic polynomial-time many-one reductions.

**Use sites.** `Complexity.paddedWeights` adds `B+1`; `padded_subset_sum_iff` proves preservation; `padded_total_exceeds`, `padded_weights_positive`, `paddedSubsetSumInput_feasible_iff` and `actual_all_skip_strictly_feasible` give the actual one-state/two-action deterministic-self-loop planning reduction for each fixed rational `0<alpha<1`. Payload-size bounds are own. External input supplies source-language hardness alone. It does not state that the P36 planner is NP-hard, nor supply the actual reduction or integer-forcing proof.

## E5. Polynomial-size rational witness for a bounded rational polytope

**Reference.** A. Schrijver, *Theory of Linear and Integer Programming*, Wiley, 1986, ISBN 9780471908548, Chapters 7–8 (polyhedra/vertices) and 10 (size/complexity). Existing record also points to the [Del Pia–Dey–Molinaro author manuscript](https://www2.isye.gatech.edu/~sdey30/QIP_NP.pdf), Sections 2.1–2.3, for the standard polynomial-size vertex consequence. No unverified verbatim numbered theorem is attributed to the book.

**Exact quantifiers.** There exists a polynomial `p` such that for all finite dimensions `d,m` and all rational matrices/vectors `A,b` of total binary length `L`, if

`P = {x in R^d | A*x <= b and 0<=x<=1}`

is nonempty, it contains a rational vertex with total binary length at most `p(L)`. For `d>=1`, after positive integer denominator clearing and with all integer coefficients including right sides bounded in absolute value by `M>=1`, a vertex can be selected from `d` independent tight rows. A common denominator and numerators satisfy `1<=q<=d!*M^d` and `|p_i|<=d!*M^d` by Cramer determinants. Dimension zero is a constant query.

**Use sites.** `Complexity.one_state_LP_certificate_exact` and `one_state_linear_system_iff` construct the exact rational LP for each guessed `b : Fin H -> Bool`: `H` real variables, `3H+2` inequalities, box bounds included, arbitrary two-action reward and either cost ordering. The generic witness theorem supplies a short rational vector; ordinary rational arithmetic checks it. It does not supply the two-piece formula, LP coefficients, CVaR semantics or source NP-membership conclusion.

## E6. Existential-real truth in PSPACE

**Reference.** J. F. Canny, “Some Algebraic and Geometric Computations in PSPACE”, STOC 1988, pp. 460–467, DOI [10.1145/62212.62257](https://doi.org/10.1145/62212.62257), source [7]; [Berkeley primary report UCB/CSD-88-439](https://www2.eecs.berkeley.edu/Pubs/TechRpts/1988/6041.html).

**Exact quantifiers.** For every finite existential ordered-real-field sentence built from polynomial equations/inequalities with binary integer coefficients, truth is decidable in space polynomial in the encoded sentence length. Positive denominator clearing permits rational coefficients. Every language admitting a deterministic polynomial-time reduction to such sentences belongs to PSPACE.

**Use sites.** `Complexity.rational_planning_encoding_exact`, `planning_polynomial_exact`, `planningPolynomial_degree` (degree at most two), `planning_variable_count` and `planning_constraint_count` give the source-specific exact mathematical encoding and polynomial cardinalities. Standard bit serialization below turns those explicit tables into the class-transfer statement. Canny supplies neither the planning witness nor its semantic iff.

## E7. Standard exact real-algebraic decision, sampling and optimization

**Reference.** S. Basu, R. Pollack and M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition, Springer, 2006, DOI [10.1007/3-540-33099-2](https://doi.org/10.1007/3-540-33099-2), source [4].

**Exact quantifiers.** For every finite semialgebraic system over the rationals, exact algorithms decide real feasibility and produce a finite real-algebraic sample description when nonempty. For a nonempty compact rationally specified semialgebraic feasible set and a continuous polynomial objective (or rational objective nonsingular there), an optimum can be represented by a finite real-algebraic description in finite time.

**Use sites.** Secondary Appendix E consequence after the own exact polynomial projection to policies and `Nested` continuity/attainment. Compactness is invoked for feasible policies; the auxiliary epigraph/threshold witness space is not asserted compact. No polynomial-time exact optimizer for the P36 planner or arbitrary real posterior draw is assumed.

## E8. Standard binary arithmetic and bounded loop composition

**Reference.** R. P. Brent and P. Zimmermann, *Modern Computer Arithmetic*, Cambridge University Press, 2010, Chapter 1, Sections 1.2, 1.3, 1.4 and 1.6; [author publication page](https://maths-people.anu.edu.au/~brent/pub/pub226.html). Existing complexity records spell out this representation boundary.

**Exact quantifiers.** There exist polynomial-time binary algorithms for signed integer addition, subtraction, comparison, multiplication, nonzero-divisor division/remainder and gcd in operand bit lengths; normalized binary rational operations/comparisons have polynomial cost in their operand lengths. For any rational-table algorithm with polynomially many such operations in input length `L` and a polynomial bound on all intermediate bit lengths, a Turing-machine implementation and explicit output serialization take polynomial time in `L`.

**Own source-specific instantiations.** The padded reduction computes `B+1`, a finite sum `C`, four fractions per stage and targets; own `Nat.size` bounds prove normalized and fully padded quadratic payload sizes. LP coefficients use a constant number of input arithmetic operations per stage, a `(3H+2)*H` matrix, and H-term target sums; denominator-product bit lengths are `O(HL)` with explicit table length `H<=L`. The degree-two ETR grammar has `O(HAS²)` monomials; noninput coefficients are `p/alpha`, raw `(a*d,b*c)` for `p=a/b`, `alpha=c/d`, hence `O(L)` bits, and finite variable labels need `O(log N)` bits. Positive denominator clearing preserves degree and inequality directions.

**New own bit-growth proof roots.** `ComplexityEncoding.HasRep` is an actual bounded integer-numerator/nonzero-denominator representation. `one_state_LP_coefficients_rep` uses exponent `(H+1)*(4*b+3)` and `one_state_LP_scalar_payload` bounds payload by `2*(H+1)*(4*b+3)+4`. `planningTerm_sum` proves the actual sparse table equals `planningPolynomial`; each atom has `4+A+A*S` terms. `planningTerm_coefficient_rep` uses exponent `2*b`, `planningTerm_scalar_payload` gives `4*b+4`, and `positive_rep` / `clear_finite_denominators` / `planningTerm_integer_clear` supply positive integer clearing with exponent `2*b*(5+A+A*S)`. These are own source encoding estimates, not external hypotheses. `one_state_LP_total_payload` gives the complete `(3H+2)*(H+1)*(2*(H+1)*(4*b+3)+4)` bound; `planningTerm_total_payload` includes both variable labels per sparse slot, and `planning_dimensions_le_scalar_count` bounds H,S,A by the explicit input scalar count. There is no remaining source-specific bit-growth narrative gap.

**Limit.** Machine encoders, multitape runtime semantics and Lean `Rat` runtime are not formalized here. The own finite mathematical constructions, LP rational coefficient bounds and explicit ETR monomial/coefficient payload bounds are Lean statements (including new `ComplexityEncoding.one_state_LP_scalar_payload`, `planningTerm_sum`, `planningTerm_scalar_payload`); the general arithmetic/serialization composition is this explicit external narrative boundary. There is no assumed polynomial-time planner or source classification. Do not report literal Lean NP/PSPACE membership predicates as proved.

## E9. General compact-section measurable optimization/selection

**Source location.** `paper.txt` Section 4's measurable-oracle setup and Appendix A.2 `[A1.SS2.p1]` / `[A1.Ex1]` invoke the measurable maximum theorem and compact optimizer sections. That local source paragraph does not attach a bibliography number. The precise general published references used here are:

- A. S. Kechris, *Classical Descriptive Set Theory*, Springer GTM 156, 1995, chapter “Uniformization Theorems”, pp. 120–128, Arsenin–Kunugui Borel uniformization, [primary publisher chapter DOI 10.1007/978-1-4612-4190-4_18](https://link.springer.com/chapter/10.1007/978-1-4612-4190-4_18).
- C. D. Aliprantis and K. C. Border, *Infinite Dimensional Analysis: A Hitchhiker’s Guide*, third edition, Springer, 2006, chapter “Measurable correspondences”, pp. 591–620, measurable maximum theorem, [primary publisher chapter DOI 10.1007/3-540-29587-9_18](https://link.springer.com/chapter/10.1007/3-540-29587-9_18).

**Primary-source provenance check.** Both publisher book/chapter pages were opened and confirm authors, edition/year, chapter names, page ranges and DOIs. The public chapter pages do not expose the precise theorem numbers. Attempts to read the original book scans were blocked by tool size limits/HTTP 403 (Kechris) and HTTP 502 (Aliprantis–Border). Secondary papers and indexed scan fragments commonly cite numbers, but those numbers are deliberately omitted here and in production comments because the exact book theorem text was not independently fetched in this review. The external contract below is explicit and the sources are distinguished from P36's own locally unnumbered Appendix A.2 invocation.

**Exact Lean contract.** `Selection.CompactSectionMaximum.{u}` is a proposition with one field `maximize`, universally quantified over **all** `X,Y : Type u`, `[MeasurableSpace X] [StandardBorelSpace X]`, `[TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]`, every correspondence `Gamma : X -> Set Y`, and every objective `f : X*Y -> R`. Its premises are:

1. `{(x,y) | y in Gamma(x)}` is measurable in the product sigma algebra;
2. for every x, `Gamma(x)` is compact and nonempty;
3. `f` is product measurable;
4. for every x, `y -> f(x,y)` is continuous.

Its conclusion is a measurable `sigma : X -> Y` such that for every x, `sigma(x) in Gamma(x)` and for every `y in Gamma(x)`, `f(x,y) <= f(x,sigma(x))`. It contains no kernel, policy, risk, reward, prior, feasibility-margin or P36-oracle predicate.

**Published-theorem relation.** This is the standard combined consequence, not a verbatim new numbered theorem: Arsenin–Kunugui gives Borel projections/uniformizations for Borel sets with sigma-compact sections; intersecting compact Polish sections with open sets gives sigma-compact sections and hence a weakly measurable correspondence. The measurable maximum theorem then gives the maximizing Borel selector for the given measurable/decision-continuous objective. The external contract preserves hypotheses needed for this route.

**Actual own instantiation and use sites.** `Selection.feasible_graph_closed` proves the actual joint risk sublevel graph is closed, using `Nested.continuous_risk`. `feasible_graph_measurable` proves the globally extended correspondence graph is Borel for a closed model support Q; outside Q its section is all policies. `feasible_section_compact` proves compactness; `feasible_section_nonempty` derives nonemptiness from the actual minimum-risk policy and model-wise strict feasibility. `exists_borel_calibration` instantiates the general theorem with all policies and negative actual nested risk, then identifies the optimum with `Nested.minimumRisk`. `exists_borel_exploitation` uses the actual feasible sections and `Nested.continuous_reward`, proving exact feasibility/optimality on Q. `exists_borel_oracles` assembles these into `BorelAlgorithm.BorelOracles`. `StageSelection.deterministicPolicies_closed` separately proves the compact pure-policy set; its `exists_borel_calibration` optimizes only over that set and proves exact actual stage DP equality plus `cal_deterministic`. The actual stage risk feasible graph/sections are proved using `StageCalibration.continuous_actualRisk`, and `StageSelection.exists_borel_exploitation`/`exists_borel_oracles` supply the complete actual stage Borel protocol. All source-space Polish/Borel instances are derived locally from the closed finite real simplex and countable products. The source's exact Borel-oracle protocol remains a faithful main-theorem input; existence is now separately derived from this general theorem.



## Original protocol inputs, separately from external theorem inputs

`SourceSystem.BayesLaw` states, for every episode k, equality almost everywhere of the conditional distributions of the latent model and the current posterior draw given the same observed full history, under the one actual `SourceProtocol.measure`. It is the exact posterior-sampler specification in Algorithm 1. The planner is a Markov kernel of observed past history only, so it cannot access the latent model or unused row tapes. The model space is standard Borel and its original probability prior is arbitrary; `SourceSystem.prior_law` and `SourceTheorems.actual_prior` preserve that input prior (and its decoded kernel pushforward) exactly. This protocol identity is not an external concentration theorem or an assumed performance statement.

The final `SourceSystem.physicalLaw`, `episodeSystem`, `toPosteriorSystem` and `exists_posteriorSystem` have no additional physical-dynamics, fresh-unused, iid-row, occupation, count-prefix or empirical-prefix premise. These are derived by the own chain `SourceStepReplay.step_summary` -> `SourcePlanBlock.local_factorization` -> `SourceFresh.actual_prefix_fresh` / `actual_context_succ` -> `SourceNativeConditional.actual_physicalLaw`, and by pure replay and the generated original iid tapes. Their owners report necessary single-file checks exit 0. `SourceFiltration.naturalFiltration`, `info_comap` and `path_measurable` derive the actual increasing analyst filtration and next-time complete-path adaptation, so the final fixed-pair certificate does not add an adaptation hypothesis.

The exact Borel-oracle and selected-policy execution identities say that this process runs the stated algorithm. They do not assume comparator symmetry, signed regret, bank deficit, confidence, calibration counts or any other source conclusion. Appendix A.2 existence is independently supplied by the own instantiation of E9. Approximate B.1 wrappers require only certificates at actual exploitation calls, with full history/private randomness allowed; their H=1 bounds reduce to the original additive error sums. None of these original protocol contracts is relabelled as an external published P36 theorem.

## Things explicitly not external inputs

- The CVaR finite primal/envelope equality, optimizer existence, tail formula, Hellinger/TV stability and hybrid perturbation.
- Lemma 2.1 or actual compactness/continuity of the source risks, calibration DP correctness, deterministic optimality or actual scalar tail scan.
- A source posterior confidence set, posterior concentration, occupancy domination, simulation bound, fixed-K certificate, calibration frequency or regret conclusion.
- Adaptive iid row-tape coupling, infinite product tapes, generic measurable-history execution, unused conditional laws, history/count-prefix identities, full trajectory conditional law, posterior symmetry, scalar multivariate polylog envelopes, actual source native filtration/adaptation and source Lemma C.3. These are now own process/measure-theoretic proofs. The final `SourceSystem.toPosteriorSystem` constructor derives all tape, freshness, physical-law, count and empirical-prefix fields; it does not assume any of those conclusions.
- The source subset-sum reduction, forced binary policy, two-piece LP coefficient system, degree-two witness soundness/completeness and explicit payload bounds.
- The actual rare-chain MDP, full feedback likelihood, no-information identity, arbitrary-private-tape learner lower bound, Bayes optimality/exact sum, fallback tradeoff or heterogeneous product-hazard result.

## Final recording / validation

Every external use should retain the above universal quantifiers and finite-input conventions. Existing records are explicit candidate boundaries; this record does not approve them globally. Source-specific boundedness, graph, semantic and coupling obligations remain linked above to their production proofs. The final original-source `SourceTheorems` (9 roots) and `SourceEndpointTheorems` (4 roots) received root-reported necessary single-file exit 0; the remaining warnings are unused binders, separately recorded in `work/root-individual-checks.json`. Full build, axiom audit, kernel replay and official Comparator positive/negative controls remain **verification_deferred_by_user**; the initial read-only review ran no compilation; the subsequently authorized Selection/StageSelection/PolylogScaling/StageParameters/SourceFiltration bridges had only their reported necessary single-file incremental checks. The new scalar and stage-parameter bridges introduce no external inputs.
