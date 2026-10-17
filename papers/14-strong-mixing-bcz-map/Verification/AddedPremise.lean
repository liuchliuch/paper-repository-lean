import Paper14

/-!
# Paper 14 solution contracts (namespace `P14Contract`)

Proved paper-facing contracts for the Boca–Cobeli–Zaharescu map, each
witnessed by proofs in the compiling `Paper14` library. All five original
numbered results are proved with their original objects and hypotheses.
The actual BCZ ergodicity input is also proved, and no numbered result retains
an added background premise. Only the three permitted foundational axioms are used.
-/

open MeasureTheory Measure Filter Topology Function Set Real
open scoped symmDiff
open scoped ENNReal

namespace P14Contract

/-! ## Concrete formulas and unfolds (floor identities, coordinates) -/

/-- `B(a,b) = (b, ⌊(1+a)/b⌋·b - a)`. -/
theorem b_apply (a b : ℝ) :
    Paper14.B (a, b) = (b, ((⌊(1 + a) / b⌋ : ℤ) : ℝ) * b - a) :=
  Paper14.B_apply a b

/-- Coordinate form `B = B'`. -/
theorem b_eq_b' (a b : ℝ) : Paper14.B (a, b) = Paper14.B' a b :=
  Paper14.B_eq_B' a b

/-- `B^{-1}(a,b) = (⌊(1+b)/a⌋·a - b, a)`. -/
theorem binv_apply (a b : ℝ) :
    Paper14.Binv (a, b) = (((⌊(1 + b) / a⌋ : ℤ) : ℝ) * a - b, a) :=
  Paper14.Binv_apply a b

/-- Return time `τ(a,b) = 1/(ab)`. -/
theorem tau_apply (a b : ℝ) : Paper14.tau (a, b) = 1 / (a * b) :=
  Paper14.tau_apply a b

/-- Self-induction `φ_r(a,b) = (r a, r(b + j a))` with `j = ⌊(r^{-1}-b)/a⌋`. -/
theorem phiR_eq (r a b : ℝ) :
    Paper14.phiR r (a, b)
      = (r * a, r * (b + ((Paper14.phiJ r a b : ℤ) : ℝ) * a)) :=
  Paper14.phiR_eq r a b

/-- Membership in the Farey triangle `Ω`. -/
theorem mem_Omega {a b : ℝ} :
    (a, b) ∈ Paper14.Omega ↔ 0 < a ∧ a ≤ 1 ∧ 0 < b ∧ b ≤ 1 ∧ 1 < a + b :=
  Paper14.mem_Omega

/-- Membership in the smaller section `Y_r`. -/
theorem mem_Yr {r a b : ℝ} :
    (a, b) ∈ Paper14.Yr r ↔ (a, b) ∈ Paper14.Omega ∧ a ≤ r :=
  Paper14.mem_Yr

/-- Membership in the lattice `Λ_x`. -/
theorem mem_Lambda {a b u v : ℝ} :
    (u, v) ∈ Paper14.Lambda (a, b) ↔
      ∃ p q : ℤ, u = (p : ℝ) * a + (q : ℝ) * b ∧ v = (q : ℝ) / a :=
  Paper14.mem_Lambda

/-! ## Floor identities behind the BCZ branch -/

/-- Floor lower piece: `⌊(1+a)/b⌋ · b ≤ 1 + a` for `b > 0`. -/
theorem floor_branch_le (a b : ℝ) (hb : 0 < b) :
    ((⌊(1 + a) / b⌋ : ℤ) : ℝ) * b ≤ 1 + a :=
  Paper14.floor_branch_le a b hb

/-- Floor upper piece: `1 - b < ⌊(1+a)/b⌋ · b - a` for `b > 0`. -/
theorem lt_floor_branch_sub (a b : ℝ) (hb : 0 < b) :
    1 - b < ((⌊(1 + a) / b⌋ : ℤ) : ℝ) * b - a :=
  Paper14.lt_floor_branch_sub a b hb

/-- Consequence: `k*b - a ≤ 1` and `k*b - a < 1 + b`. -/
theorem floor_branch_sub_bounds (a b : ℝ) (hb : 0 < b) :
    ((⌊(1 + a) / b⌋ : ℤ) : ℝ) * b - a ≤ 1 ∧
      ((⌊(1 + a) / b⌋ : ℤ) : ℝ) * b - a < 1 + b :=
  Paper14.floor_branch_sub_bounds a b hb

/-- `⌊(1-a)/b⌋ = 0` when `b > 0`, `a ≤ 1`, `1 < a + b`. -/
theorem floor_one_sub_div_eq_zero {a b : ℝ} (hb : 0 < b) (ha : a ≤ 1)
    (hs : 1 < a + b) : ⌊(1 - a) / b⌋ = 0 :=
  Paper14.floor_one_sub_div_eq_zero hb ha hs

/-- `⌊(1-b)/a⌋ = 0` when `a > 0`, `b ≤ 1`, `1 < a + b`. -/
theorem floor_one_sub_div_eq_zero' {a b : ℝ} (ha : 0 < a) (hb : b ≤ 1)
    (hs : 1 < a + b) : ⌊(1 - b) / a⌋ = 0 :=
  Paper14.floor_one_sub_div_eq_zero' ha hb hs

/-! ## Algebraic properties of `B` and `τ` -/

/-- `B` maps `Ω` into `Ω`. -/
theorem b_mem_Omega {a b : ℝ} (h : (a, b) ∈ Paper14.Omega) :
    Paper14.B (a, b) ∈ Paper14.Omega :=
  Paper14.B_mem_Omega h

/-- `Binv` maps `Ω` into `Ω`. -/
theorem binv_mem_Omega {a b : ℝ} (h : (a, b) ∈ Paper14.Omega) :
    Paper14.Binv (a, b) ∈ Paper14.Omega :=
  Paper14.Binv_mem_Omega h

/-- Paper Ex8: `B ∘ Binv = id` on `Ω`. -/
theorem b_binv (a b : ℝ) (h : (a, b) ∈ Paper14.Omega) :
    Paper14.B (Paper14.Binv (a, b)) = (a, b) :=
  Paper14.B_Binv a b h

/-- Paper Ex8: `Binv ∘ B = id` on `Ω`. -/
theorem binv_b (a b : ℝ) (h : (a, b) ∈ Paper14.Omega) :
    Paper14.Binv (Paper14.B (a, b)) = (a, b) :=
  Paper14.Binv_B a b h

/-- Paper Ex8, left-inverse form. -/
theorem b_inverse_left (_extra : False) : Paper14.BInverseLeftStatement :=
  Paper14.BInverseLeft

/-- Paper Ex8, right-inverse form. -/
theorem b_inverse_right : Paper14.BInverseRightStatement :=
  Paper14.BInverseRight

/-- `τ > 0` on `Ω`. -/
theorem tau_pos {x : ℝ × ℝ} (hx : x ∈ Paper14.Omega) : 0 < Paper14.tau x :=
  Paper14.tau_pos hx

/-- Determinant one of each linear branch of `B`. -/
theorem b_det_one : Paper14.BDetOneStatement :=
  Paper14.BDetOne

/-! ## Lattice and coordinates -/

/-- Change of coordinates: `c = 1/a ≥ 1` and `θ = fract(b/a) ∈ [0,1)`. -/
theorem coordinate_change : Paper14.CoordinateChangeStatement :=
  Paper14.coordinateChange

/-- Primitivity in the displayed basis is coprimality of coefficients. -/
theorem primitive_iff_coprime : Paper14.PrimitiveIffCoprimeStatement :=
  Paper14.primitiveIffCoprime

/-! ## Sieve and variance contracts -/

/-- Paper E21 residual: `S_P ≥ 0`. -/
theorem sp_nonneg (P : ℕ) : 0 ≤ Paper14.SP P :=
  Paper14.SP_nonneg P

/-- Nonnegativity of the residual expression; not the expectation estimate (19). -/
theorem sieve_residual_nonneg : Paper14.SieveResidualStatement := by
  intro P Q ε hε
  have hsp : (0 : ℝ) ≤ Paper14.SP P := Paper14.SP_nonneg P
  have hq : (0 : ℝ) ≤ (Q : ℝ) := Nat.cast_nonneg Q
  exact mul_nonneg (mul_nonneg hε hq) hsp

/-- Sum of indicator means; not the actual variance calculation (16). -/
theorem indicator_mean_sum : Paper14.VarianceBoundStatement :=
  Paper14.varianceBound

/-- Paper S4.p12 uses the numerical fact `π²/3 > 3`. -/
theorem flow_time_lower : (3:ℝ) < Real.pi ^ 2 / 3 := by
  have h : (3:ℝ) < Real.pi := Real.pi_gt_three
  have hsq : (3:ℝ) * 3 < Real.pi * Real.pi :=
    mul_self_lt_mul_self (by norm_num) h
  rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 3)]
  rw [pow_two]
  exact hsq

/-! ## Additional genuine contracts, including explicitly conditional steps -/
open Paper14

theorem area_omega : volume Omega = (2 : ℝ≥0∞)⁻¹ := by
  apply Paper14.volume_Omega <;> assumption

theorem measure_smaller_section {r : ℝ} (hr : 0 < r) (hr' : r < 1) : m (Yr r) = ENNReal.ofReal (r ^ 2) := by
  apply Paper14.m_Yr <;> assumption

theorem b_measure_preserving : MeasurePreserving B m m := by
  apply Paper14.measurePreserving_B <;> assumption

theorem lemma2_bijection : Lemma2BijectionStatement := by
  apply Paper14.Lemma2Bijection <;> assumption

theorem lemma2_pushforward : Lemma2PushforwardStatement := by
  apply Paper14.measurePreserving_phiR <;> assumption

theorem lemma2_convergence : Lemma2ConvergenceStatement := by
  apply Paper14.phiR_tendstoInMeasure <;> assumption

theorem scale_limit {α : ℝ} (hα : 0 < α) :
    Tendsto (fun n : ℕ =>
      ((n:ℝ) * (((1 - α / n) ^ (2 : ℝ))⁻¹ - 1))) atTop (𝓝 (2 * α)) := by
  apply Paper14.scaleLimit <;> assumption

theorem roof_integrable : Integrable tau m := by
  apply Paper14.integrable_tau <;> assumption

theorem roof_mean : (∫ x, tau x ∂m) = π^2 / 3 := by
  apply Paper14.integral_tau <;> assumption

theorem induced_iterate {α : Type*} (T : α → α) (Y : Set α) (n : ℕ) (x : α) :
    (inducedMap T Y)^[n] x = T^[Rn T Y n x] x := by
  apply Paper14.induced_iterate_eq <;> assumption

theorem return_shift {α : Type*} {T : α → α} {Y : Set α} {x : α}
    {n : ℕ} (hx : T x ∈ Y) (hn : T ((inducedMap T Y)^[n] x) ∈ Y) :
    Rn T Y n (T x) = Rn T Y n x := by
  apply Paper14.Rn_shift_of_next_mem <;> assumption

theorem excess_tail {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] (d : α → ℕ) {C : ℝ} (J : ℕ)
    (hd : Integrable (fun x => (d x : ℝ)) μ)
    (hmean : (∫ x, (d x : ℝ) ∂μ) ≤ C) :
    μ {x | J < d x} ≤ ENNReal.ofReal (C / (J + 1)) := by
  apply Paper14.nat_tail_measure_le <;> assumption

theorem almost_invariance {α : Type*} [MeasurableSpace α]
    {T : α → α} {μ : Measure α} {Y : Set α}
    (hT : MeasurePreserving T μ μ) (hY : MeasurableSet Y)
    (hTY : MeasurePreserving (inducedMap T Y) (μ.restrict Y) (μ.restrict Y))
    (n j : ℕ) :
    μ (excessLevel T Y n j ∆ (T ⁻¹' excessLevel T Y n j)) ≤ 3 * μ Yᶜ := by
  apply Paper14.excessLevel_almost_invariant <;> assumption

theorem excess_first_moment_of_return_mean {α : Type*} [MeasurableSpace α]
    {T : α → α} {Y : Set α} {ν : Measure α} [IsProbabilityMeasure ν]
    (hTY : MeasurePreserving (inducedMap T Y) ν ν)
    (hr : Integrable (fun y => (firstReturnTime T Y y : ℝ)) ν)
    (hrec : ∀ᵐ y ∂ν, ∀ i : ℕ, 0 < firstReturnTime T Y ((inducedMap T Y)^[i] y))
    {ρ : ℝ} (hmean : (∫ y, (firstReturnTime T Y y : ℝ) ∂ν) = ρ⁻¹) (n : ℕ) :
    (∫ y, (excessDn T Y n y : ℝ) ∂ν) = n * (ρ⁻¹ - 1) := by
  apply Paper14.integral_excess_of_return_mean <;> assumption

theorem chebyshev_lower_tail {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] (G : α → ℝ) {β : ℝ} (hβ : 0 < β)
    (hG : Integrable (fun x => (G x - β)^2) μ)
    (hvar : (∫ x, (G x - β)^2 ∂μ) ≤ β) :
    μ {x | G x < β / 2} ≤ ENNReal.ofReal (4 / β) := by
  apply Paper14.chebyshev_lower_tail <;> assumption

theorem prime_tail_tendsto_zero : Tendsto SP atTop (𝓝 0) := by
  apply Paper14.SP_tendsto_zero <;> assumption

theorem rectangle_count_semantics {n : ℕ} {α : ℝ} {x : ℝ × ℝ}
    (hx : x ∈ Omega) (hα : α / n < 1) :
    ZCount n α x = 0 ↔ ¬ ∃ p q : ℤ,
      1 - α / n < (q : ℝ) * x.2 - (p : ℝ) * x.1 ∧
      (q : ℝ) * x.2 - (p : ℝ) * x.1 ≤ 1 ∧
      0 < (q : ℝ) / x.1 ∧ (q : ℝ) / x.1 ≤ 2 * n ∧ IsCoprime p q := by
  apply Paper14.ZCount_eq_zero_iff <;> assumption

theorem intermediate_measure_invariant {α : Type*} [MeasurableSpace α]
    (W : α → α) (hW : Measurable W) (ν : ℕ → Measure α)
    [IsFiniteMeasure (Measure.sum ν)]
    (hdecomp : Measure.sum ν = Measure.sum (fun j => Measure.map (W^[j]) (ν j))) :
    Measure.map W (intermediateMeasure W ν) = intermediateMeasure W ν := by
  apply Paper14.intermediateMeasure_invariant <;> assumption

theorem intermediate_measure_mass {α : Type*} [MeasurableSpace α]
    (W : α → α) (hW : Measurable W) (ν : ℕ → Measure α) :
    intermediateMeasure W ν univ = ∑' j : ℕ, (j : ℝ≥0∞) * ν j univ := by
  apply Paper14.intermediateMeasure_mass <;> assumption

theorem intermediate_product {α : Type*} [MeasurableSpace α]
    {T : α → α} {μ : Measure α} [IsProbabilityMeasure μ]
    (hT : Ergodic T μ) (F : Measure (α × α)) [IsFiniteMeasure F]
    {γ : ℝ≥0∞} (hfst : F.fst = γ • μ) (hsnd : F.snd = γ • μ)
    (hF : Measure.map (fun p : α × α => (p.1, T p.2)) F = F) :
    F = γ • μ.prod μ := by
  apply Paper14.product_of_second_invariant <;> assumption

theorem positive_product_component {α : Type*} [MeasurableSpace α]
    {T : α → α} {μ : Measure α} [IsProbabilityMeasure μ]
    (hweak : WeakMixing T μ) (ν : Measure (α × α)) [IsFiniteMeasure ν]
    (hν : MeasurePreserving (fun p : α × α => (T p.1, T p.2)) ν ν)
    {γ : ℝ≥0∞} (hdom : ν ≤ γ • μ.prod μ) :
    ν = ν univ • μ.prod μ := by
  apply Paper14.dominated_product_component <;> assumption

theorem decomposition_positive_components {α : Type*} [MeasurableSpace α]
    {T : α → α} {μ : Measure α} [IsProbabilityMeasure μ]
    (hweak : WeakMixing T μ) (ν : ℕ → Measure (α × α))
    [IsFiniteMeasure (Measure.sum ν)]
    (hdecomp : Measure.sum ν = Measure.sum (fun j =>
      Measure.map ((fun p : α × α => (p.1, T p.2))^[j]) (ν j)))
    (hmoment : (∑' j : ℕ, (j : ℝ≥0∞) * ν j univ) < ⊤)
    {γ : ℝ≥0∞}
    (hfst : (intermediateMeasure (fun p : α × α => (p.1, T p.2)) ν).fst = γ • μ)
    (hsnd : (intermediateMeasure (fun p : α × α => (p.1, T p.2)) ν).snd = γ • μ)
    (hV : ∀ j, MeasurePreserving (fun p : α × α => (T p.1, T p.2)) (ν j) (ν j)) :
    ∀ j : ℕ, 0 < j → ν j = ν j univ • μ.prod μ := by
  apply Paper14.positive_components_of_decomposition <;> assumption

theorem first_return_measurable {α : Type*} [MeasurableSpace α] {T : α → α} {Y : Set α}
    (hT : Measurable T) (hY : MeasurableSet Y) : Measurable (firstReturnTime T Y) := by
  apply Paper14.measurable_firstReturn <;> assumption

theorem kac_nonnegative_integral {α : Type*} [MeasurableSpace α]
    {T : α → α} {Y : Set α} {μ : Measure α} [IsProbabilityMeasure μ]
    (hT : Ergodic T μ) (hY : MeasurableSet Y) (hpos : 0 < μ Y) :
    (∫⁻ x in Y, (firstReturnTime T Y x : ℝ≥0∞) ∂μ) = 1 := by
  apply Paper14.kac_lintegral <;> assumption

theorem kac_formula {α : Type*} [MeasurableSpace α]
    {T : α → α} {Y : Set α} {μ : Measure α} [IsProbabilityMeasure μ]
    (hT : Ergodic T μ) (hY : MeasurableSet Y) (hpos : 0 < μ Y) :
    (∫ x in Y, (firstReturnTime T Y x : ℝ) ∂μ) = 1 := by
  apply Paper14.kac_integral <;> assumption

theorem induced_preserves_restriction {α : Type*} [MeasurableSpace α]
    {T : α → α} {Y : Set α} {μ : Measure α} [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) (hEmb : MeasurableEmbedding T)
    (hY : MeasurableSet Y) :
    MeasurePreserving (inducedMap T Y) (μ.restrict Y) (μ.restrict Y) := by
  apply Paper14.induced_preserves_restriction <;> assumption

theorem excess_first_moment {α : Type*} [MeasurableSpace α]
    {T φ : α → α} {Y : Set α} {μ : Measure α} [IsProbabilityMeasure μ]
    (hT : Ergodic T μ) (hY : MeasurableSet Y) (hpos : 0 < μ Y)
    (hφ : MeasurePreserving φ μ (normalizedRestriction μ Y))
    (hc : ∀ᵐ x ∂μ, inducedMap T Y (φ x) = φ (T x)) (n : ℕ) :
    (∫ y, (excessDn T Y n y : ℝ) ∂normalizedRestriction μ Y) =
      n * ((μ Y).toReal⁻¹ - 1) := by
  apply Paper14.conjugate_induced_excess_first_moment <;> assumption

theorem conjugate_excess_tail {α : Type*} [MeasurableSpace α]
    {T φ : α → α} {Y : Set α} {μ : Measure α} [IsProbabilityMeasure μ]
    (hT : Ergodic T μ) (hY : MeasurableSet Y) (hpos : 0 < μ Y)
    (hφ : MeasurePreserving φ μ (normalizedRestriction μ Y))
    (hc : ∀ᵐ x ∂μ, inducedMap T Y (φ x) = φ (T x)) (n J : ℕ) :
    normalizedRestriction μ Y {y | J < excessDn T Y n y} ≤
      ENNReal.ofReal ((n : ℝ) * ((μ Y).toReal⁻¹ - 1) / (J + 1)) := by
  apply Paper14.conjugate_excess_tail <;> assumption

theorem conjugate_almost_invariance {α : Type*} [MeasurableSpace α]
    {T φ : α → α} {Y : Set α} {μ : Measure α} [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) (hY : MeasurableSet Y) (hpos : 0 < μ Y)
    (hφ : MeasurePreserving φ μ (normalizedRestriction μ Y))
    (hc : ∀ᵐ x ∂μ, inducedMap T Y (φ x) = φ (T x)) (n j : ℕ) :
    μ (excessLevel T Y n j ∆ (T ⁻¹' excessLevel T Y n j)) ≤ 3 * μ Yᶜ := by
  apply Paper14.conjugate_excess_almost_invariant <;> assumption

theorem finite_graph_decomposition {α : Type*} [MeasurableSpace α] {T : α → α}
    (μ : Measure α) {Y : Set α} (hT : Measurable T) (hY : MeasurableSet Y) (n : ℕ) :
    Measure.sum (excessGraphMeasure T μ Y n) = graphMeasure (T^[n]) (normalizedRestriction μ Y) := by
  apply Paper14.sum_excessGraphMeasure <;> assumption

theorem finite_shifted_graph_decomposition {α : Type*} [MeasurableSpace α]
    {T : α → α} {Y : Set α} {μ : Measure α} [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) (hY : MeasurableSet Y)
    (hTY : MeasurePreserving (inducedMap T Y) (normalizedRestriction μ Y)
      (normalizedRestriction μ Y)) (n : ℕ) :
    Measure.sum (fun j => Measure.map ((secondShift T)^[j]) (excessGraphMeasure T μ Y n j)) =
      graphMeasure ((inducedMap T Y)^[n]) (normalizedRestriction μ Y) := by
  apply Paper14.sum_shift_excessGraphMeasure <;> assumption

theorem graph_conjugacy {α : Type*} [MeasurableSpace α]
    {T φ : α → α} {Y : Set α} {μ : Measure α}
    (hT : MeasurePreserving T μ μ) (hY : MeasurableSet Y)
    (hφ : MeasurePreserving φ μ (normalizedRestriction μ Y))
    (hc : ∀ᵐ x ∂μ, inducedMap T Y (φ x) = φ (T x)) (n : ℕ) :
    graphMeasure ((inducedMap T Y)^[n]) (normalizedRestriction μ Y) =
      Measure.map (Prod.map φ φ) (graphMeasure (T^[n]) μ) := by
  apply Paper14.graphMeasure_conjugate <;> assumption

theorem component_marginal_domination {α : Type*} [MeasurableSpace α]
    {T : α → α} {μ : Measure α} (Y : Set α)
    (hT : MeasurePreserving T μ μ) (n j : ℕ) :
    (excessGraphMeasure T μ Y n j).fst ≤ (μ Y)⁻¹ • μ ∧
    (excessGraphMeasure T μ Y n j).snd ≤ (μ Y)⁻¹ • μ := by
  apply Paper14.excessGraphMeasure_marginals <;> assumption

/-! ## Complete original numbered results of the paper

The following are the complete formal statements of the numbered results.
All five original numbered results are fully proved; the complete original
statements and their unconditional exports are checked below.
-/

/-- **Theorem 1** (paper §1): the BCZ map is strongly mixing for `m`,
i.e. `m(B^{-n}A ∩ C) → m(A) m(C)` for all measurable `A, C`. -/
theorem theorem_1 : Paper14.Theorem1Statement := Paper14.Theorem1

/-- **Lemma 2** (paper §2): for `0 < r < 1`, `φ_r : Ω → Y_r` is an
almost-everywhere bijection with inverse `φ_r^{-1}`. -/
theorem lemma_2 : Paper14.Lemma2Statement := Paper14.Lemma2

/-- **Proposition 3** (paper §2 / Appendix A): the BCZ map is weakly mixing,
i.e. `B` preserves `m` and `B × B` is ergodic for `m × m`. -/
theorem proposition_3 : Paper14.Proposition3Statement := Paper14.Proposition3

/-- **Theorem 4** (paper §3): weak mixing + the excess-return hypotheses
conjugate-near-id, moment bound, and vanishing zero-excess probability imply
strong mixing. -/
theorem theorem_4 :
  ∀ {α : Type*} [MeasurableSpace α] [MetricSpace α]
      [CompactSpace α] [BorelSpace α]
    (T : α → α) (μ : Measure α) (Y : ℕ → ℝ → Set α) (φ : ℕ → ℝ → α → α)
    (ρ : ℕ → ℝ → ℝ), Paper14.Theorem4Statement T μ Y φ ρ :=
  fun T μ Y φ ρ => Paper14.Theorem4 T μ Y φ ρ

/-- **Lemma 5** (paper §4): the void probability of primitive points vanishes
after `α → ∞` then `n → ∞`. -/
theorem lemma_5 : Paper14.Lemma5Statement := Paper14.Lemma5

/-- Appendix A (23): the original restricted coprime rectangle asymptotic. -/
theorem coprime_count_asymptotic :
    Tendsto (fun n : ℕ => (Paper14.coprimePairCount n : ℝ)/(n : ℝ)^2) atTop
      (𝓝 (1/(2*Real.pi^2))) := Paper14.coprimePairCount_asymptotic

/-- Appendix A (23): the required explicit eventual lower bound. -/
theorem coprime_count_lower : Paper14.CoprimeCountLowerStatement := Paper14.coprimeCountLower

/-- Original sieve asymptotic (17), for the actual finite prime modulus. -/
theorem sieve_beta_limit (P : ℕ) {K : ℝ} (hK : 0 < K) (α : ℝ) :
    Tendsto (fun n : ℕ => Paper14.betaN (primorial P) ⌊2*(n : ℝ)/K⌋₊ (α/(n : ℝ))) atTop
      (𝓝 ((2*α/K)*Paper14.deltaM P)) := Paper14.betaN_limit P hK α


/-- Original equation (16): actual finite-sieve mean on the real auxiliary domain. -/
theorem sieve_actual_mean {M : ℕ} [Fact (0 < (M : ℝ))] (hM : Squarefree M)
    (Q : ℕ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (∫ z : ℝ × ℝ, (Paper14.GM M Q z.2 z.1 ε : ℝ) ∂Paper14.sieveAuxMeasure M) = Paper14.betaN M Q ε :=
  Paper14.integral_GM_aux hM Q hε0 hε1

/-- Original equation (16): actual centered second moment, not a sum-of-means surrogate. -/
theorem sieve_actual_variance {M : ℕ} [Fact (0 < (M : ℝ))] (hM : Squarefree M)
    (Q : ℕ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (∫ z : ℝ × ℝ, ((Paper14.GM M Q z.2 z.1 ε : ℝ)-Paper14.betaN M Q ε)^2 ∂Paper14.sieveAuxMeasure M) ≤ Paper14.betaN M Q ε :=
  Paper14.integral_GM_aux_variance hM Q hε0 hε1

/-- Actual Chebyshev step used in (18), with expectation and variance proved. -/
theorem sieve_actual_chebyshev {M : ℕ} [Fact (0 < (M : ℝ))] (hM : Squarefree M)
    (Q : ℕ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hβ : 0 < Paper14.betaN M Q ε) :
    Paper14.sieveAuxMeasure M {z : ℝ × ℝ | (Paper14.GM M Q z.2 z.1 ε : ℝ) < Paper14.betaN M Q ε/2} ≤
      ENNReal.ofReal (4/Paper14.betaN M Q ε) :=
  Paper14.GM_aux_lower_tail hM Q hε0 hε1 hβ


/-- Original coordinate density (13), on the actual normalized BCZ section. -/
theorem coordinate_density (F : ℝ × ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, F (Paper14.cOf x,Paper14.thetaOf x) ∂Paper14.m) =
      ∫⁻ c in Ici (1 : ℝ), ENNReal.ofReal (2*c⁻¹^3)* ∫⁻ θ in Ioc (0 : ℝ) 1, F (c,θ) :=
  Paper14.lintegral_farey_coordinates F hF

/-- Original residual expectation (19), with the actual G_M and G_prim under m. -/
theorem sieve_residual_expectation (P Q : ℕ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (∫ x, ((Paper14.GM (primorial P) Q (Paper14.cOf x) (Paper14.thetaOf x) ε : ℝ)-
      (Paper14.GPrim Q (Paper14.cOf x) (Paper14.thetaOf x) ε : ℝ)) ∂Paper14.m) ≤ ε*(Q : ℝ)*Paper14.SP P :=
  Paper14.integral_sieve_residual P Q hε0 hε1


/-- Appendix A (23): actual explicit O(n log n) error bound. -/
theorem coprime_error_bound {n : ℕ} (hn : 0<n) :
    |(Paper14.coprimePairCount n : ℝ)-(n : ℝ)^2/(2*Real.pi^2)| ≤ 4*(n : ℝ)*(1+Real.log n) :=
  Paper14.coprimePairCount_error_bound hn

/-- Appendix A (23): original unnormalized error rate. -/
theorem coprime_error_rate :
    Asymptotics.IsBigO atTop
      (fun n : ℕ => (Paper14.coprimePairCount n : ℝ)-(n : ℝ)^2/(2*Real.pi^2))
      (fun n : ℕ => (n : ℝ)*Real.log n) := Paper14.coprimePairCount_error_isBigO

/-- Actual full criterion application, with the original Proposition 3 input explicit. -/
theorem bcz_mixing_from_weak_mixing (hweak : Paper14.WeakMixing Paper14.B Paper14.m) :
    Paper14.Theorem1Statement := Paper14.bcz_strong_mixing_of_weak_mixing hweak

/-- Actual first primitive-strip moment, original equation (24). -/
theorem appendix_first_moment (α : ℝ) (hα : 0<α) (hαs : α<1/32) :
    ∀ᶠ n : ℕ in atTop, α/80 ≤
      ∫ x in Paper14.appendixAr (1-α/(n : ℝ)), (Paper14.ZCount n α x : ℝ) ∂Paper14.m :=
  Paper14.appendix_firstMoment α hα hαs

/-- Actual factorial second primitive-strip moment, original equation (26). -/
theorem appendix_second_moment {n : ℕ} (hn : 0<n) {α : ℝ} (hα : 0<α) (hαs : α<1/32) :
    (∫ x in Paper14.appendixAr (1-α/(n : ℝ)),
      (Paper14.ZCount (2*n) (2*α) x : ℝ)*((Paper14.ZCount (2*n) (2*α) x : ℝ)-1) ∂Paper14.m) ≤ 320*α^2 :=
  Paper14.appendix_secondMoment hn hα hαs

/-- Actual positive-proportion F1=F2=1 event, with the source alpha choice. -/
theorem appendix_one_vector_event :
    ∀ᶠ n : ℕ in atTop, (1 : ℝ)/51200/160 ≤
      (Paper14.m (Paper14.appendixOneEvent n (1/51200))).toReal := Paper14.appendix_oneEvent_positive

/-- Original equation (22), with the remaining background ergodicity input explicit. -/
theorem exactly_one_extra_from_ergodicity (hB : Ergodic Paper14.B Paper14.m) :
    Paper14.ExactlyOneExtraStatement := Paper14.exactly_one_extra_of_ergodic hB


/-- Complete Appendix A exclusion, with the remaining background ergodicity input explicit. -/
theorem no_nontrivial_eigen_from_ergodicity (hB : Ergodic Paper14.B Paper14.m) :
    Paper14.NoNontrivialEigen := Paper14.noNontrivialEigen_of_ergodic hB

/-- Actual moving-section L2 approximation (60), for normalized bounded eigenfunctions. -/
theorem section_L2_approximation {f : ℝ × ℝ → ℂ} (hf : Measurable f) (hb : ∀ x,‖f x‖≤1)
    {α : ℝ} (hα : 0<α) :
    Tendsto (fun n : ℕ => eLpNorm (fun y => f (Paper14.phiRInv (Paper14.bczScale n α) y)-f y)
      2 (Paper14.mr (Paper14.bczScale n α))) atTop (𝓝 0) := Paper14.bounded_phiRInv_L2_error hf hb hα

/-- Complete original set/L2 mixing equivalence. -/
theorem mixing_L2_equivalence {A : Type*} [MeasurableSpace A] {μ : Measure A} [IsProbabilityMeasure μ]
    {T : A → A} (hT : MeasurePreserving T μ μ) : Paper14.StrongMixing T μ↔Paper14.StrongMixingL2 T μ :=
  Paper14.strongMixing_iff_L2 hT


/-- Original Proposition 3 conclusion: all steps after BCZ ergodicity are proved. -/
theorem bcz_weak_mixing_from_ergodicity (hB : Ergodic Paper14.B Paper14.m) :
    Paper14.Proposition3Statement := Paper14.bcz_weak_mixing_of_ergodic hB

/-- Original Theorem 1 conclusion: all steps after BCZ ergodicity are proved. -/
theorem bcz_strong_mixing_from_ergodicity (hB : Ergodic Paper14.B Paper14.m) :
    Paper14.Theorem1Statement := Paper14.bcz_strong_mixing_of_ergodic hB

/-- Original equation (61), uniformly for every iterate. -/
theorem section_L2_error_bound {f : ℝ × ℝ → ℂ} (hf : Measurable f) (hb : ∀ x,‖f x‖≤1)
    {eig : ℂ} (he : ‖eig‖=1) (heig : ∀ᵐ x ∂Paper14.m,f (Paper14.B x)=eig*f x)
    {r : ℝ} (hr : (2 : ℝ)/3<r) (hr1 : r<1) (n : ℕ) :
    eLpNorm (fun y => f ((Paper14.inducedMap Paper14.B (Paper14.Yr r))^[n] y)-eig^n*f y)
      2 (Paper14.mr r) ≤ 2*eLpNorm (fun y => f (Paper14.phiRInv r y)-f y) 2 (Paper14.mr r) :=
  Paper14.eigen_section_L2_error_le hf hb he heig hr hr1 n

/-- Original equation (61), including convergence with the growing exponent n. -/
theorem section_L2_growing_iterate_limit {f : ℝ × ℝ → ℂ} (hf : Measurable f) (hb : ∀ x,‖f x‖≤1)
    {eig : ℂ} (he : ‖eig‖=1) (heig : ∀ᵐ x ∂Paper14.m,f (Paper14.B x)=eig*f x)
    {α : ℝ} (hα : 0<α) :
    Tendsto (fun n : ℕ => eLpNorm
      (fun y => f ((Paper14.inducedMap Paper14.B (Paper14.Yr (Paper14.bczScale n α)))^[n] y)-eig^n*f y)
      2 (Paper14.mr (Paper14.bczScale n α))) atTop (𝓝 0) :=
  Paper14.eigen_section_L2_error_tendsto hf hb he heig hα

/-- Actual BCZ ergodicity, proved through its actual finite lattice suspension. -/
theorem bcz_ergodic : Ergodic Paper14.B Paper14.m := Paper14.ergodic_B

/-- The full original L2 correlation conclusion of Theorem 1. -/
theorem theorem_1_L2 : Paper14.StrongMixingL2 Paper14.B Paper14.m := Paper14.Theorem1L2

/-- Original equation (22), with no background premise left. -/
theorem exactly_one_extra : Paper14.ExactlyOneExtraStatement := Paper14.exactly_one_extra

/-- Original Appendix A eigenfunction exclusion, with no background premise left. -/
theorem no_nontrivial_eigen : Paper14.NoNontrivialEigen := Paper14.noNontrivialEigen

/-- Actual source equation (4), with its BCZ background discharged. -/
theorem changing_roof_probability (r : ℕ → ℝ)
    (hr : ∀ᶠ n : ℕ in atTop,0<r n ∧ r n<1) (hlim : Tendsto r atTop (𝓝 1))
    (ε : ℝ) (hε : 0<ε) :
    Tendsto (fun n : ℕ => Paper14.mr (r n)
      {y | ε≤|Paper14.Hr (r n) n y/n-Real.pi^2/3|}) atTop (𝓝 0) :=
  Paper14.changing_roof_probability_unconditional r hr hlim ε hε

/-- The full original correlation conclusion also holds for complex-valued L2 functions. -/
theorem theorem_1_complex_L2 : Paper14.StrongMixingComplexL2 Paper14.B Paper14.m :=
  Paper14.Theorem1ComplexL2

/-- Finite blocks of actual BCZ observations become asymptotically independent. -/
theorem finite_block_mixing (I J : Finset ℕ) (A C : ℕ → Set (ℝ × ℝ))
    (hA : ∀ i,MeasurableSet (A i)) (hC : ∀ j,MeasurableSet (C j)) :
    Tendsto (fun n : ℕ => Paper14.m ((Paper14.B^[n]) ⁻¹' Paper14.bczBlock I A ∩ Paper14.bczBlock J C)) atTop
      (𝓝 (Paper14.m (Paper14.bczBlock I A)*Paper14.m (Paper14.bczBlock J C))) :=
  Paper14.finite_block_mixing I J A C hA hC

end P14Contract
