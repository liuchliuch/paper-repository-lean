import Paper08.LowDegreeAlgorithm
import Paper08.BitComplexity
import Paper08.Cor13

/-! # Reduced rational sizes and the degree-one branch of Corollary 1.3 -/
noncomputable section
open scoped BigOperators
namespace Paper08.LowDegreeAlgorithm
open Integral Oracle

lemma nat_isDyadicAt (U b : ℕ) : IsDyadicAt b (U : ℚ) := by
  refine ⟨(U : ℤ) * 2 ^ b, ?_⟩
  push_cast
  field_simp

lemma projectQ_isDyadicAt (U b : ℕ) (y : ℚ) (hy : IsDyadicAt b y) :
    IsDyadicAt b (projectQ U y) := by
  unfold projectQ
  rcases le_total (U : ℚ) (max 1 y) with h | h
  · rw [min_eq_left h]
    exact nat_isDyadicAt U b
  · rw [min_eq_right h]
    rcases le_total (1 : ℚ) y with h | h
    · rw [max_eq_right h]; exact hy
    · rw [max_eq_left h]; exact isDyadicAt_one b

lemma sampleQ_isDyadicAt {n r m L : ℕ} (E : FactorFamily n r m)
    (query : (e : Fin m) → (Fin (E e).scope.card → ℚ) → ℕ → ℚ)
    (U b : ℕ) (C : Finset (Fin n)) (z : CellGrid.Grid (levels C L)) (e : Fin m) :
    IsDyadicAt b (sampleQ E query U b C z e) :=
  projectQ_isDyadicAt U b _ (dyadQ_isDyadicAt _ _)

/-- The actual component average has a single explicit dyadic denominator. -/
theorem componentEstimateQ_isDyadicAt {n r m : ℕ} (E : FactorFamily n r m)
    (query : (e : Fin m) → (Fin (E e).scope.card → ℚ) → ℕ → ℚ)
    (U b L : ℕ) (C : Finset (Fin n)) :
    IsDyadicAt (b * (blockFactors E C).card + L * C.card) (componentEstimateQ E query U b L C) := by
  apply IsDyadicAt.sum
  intro z _
  have hp := IsDyadicAt.prod (blockFactors E C) (sampleQ E query U b C z) b
    (fun e _ => sampleQ_isDyadicAt E query U b C z e)
  have hw := isDyadicAt_inv_two_pow (∑ v, levels C L v)
  have hh := hw.mul hp
  unfold CellGrid.weightQ at hh
  convert hh using 1 <;> rw [sum_levels] <;> ring

/-- The reduced denominator of the actual final rational output divides a power
with an exponent linear in the variable count and the chosen precisions. -/
theorem outputQ_isDyadicAt {n r m Δ : ℕ} (E : FactorFamily n r m)
    (query : (e : Fin m) → (Fin (E e).scope.card → ℚ) → ℕ → ℚ)
    (hdeg : FamilyPrimalDegreeLe E 1) (hocc : FamilyBoundedOccurrence E Δ) (U b L : ℕ) :
    IsDyadicAt (n * (b * (2 * Δ) + 2 * L)) (outputQ E query U b L) := by
  have hh := IsDyadicAt.prod (blocks E) (componentEstimateQ E query U b L)
    (b * (2 * Δ) + 2 * L) (fun C hC =>
      (componentEstimateQ_isDyadicAt E query U b L C).mono (by
        have ht := blockFactors_card_le E hdeg hocc hC
        have hc := block_card_le_two E hdeg hC
        nlinarith))
  exact hh.mono (by
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_left
      (b * (2 * Δ) + 2 * L) (blocks_card_le E))

theorem outputQ_den_dvd {n r m Δ : ℕ} (E : FactorFamily n r m)
    (query : (e : Fin m) → (Fin (E e).scope.card → ℚ) → ℕ → ℚ)
    (hdeg : FamilyPrimalDegreeLe E 1) (hocc : FamilyBoundedOccurrence E Δ) (U b L : ℕ) :
    (outputQ E query U b L).den ∣ 2 ^ (n * (b * (2 * Δ) + 2 * L)) :=
  (outputQ_isDyadicAt E query hdeg hocc U b L).den_dvd

lemma componentEstimateQ_le {n r m : ℕ} (E : FactorFamily n r m)
    (query : (e : Fin m) → (Fin (E e).scope.card → ℚ) → ℕ → ℚ)
    (U b L : ℕ) (hU : 1 ≤ U) (C : Finset (Fin n)) :
    (componentEstimateQ E query U b L C : ℝ) ≤ (U : ℝ) ^ (blockFactors E C).card := by
  unfold componentEstimateQ
  push_cast
  calc
    _ ≤ ∑ _z : CellGrid.Grid (levels C L), (CellGrid.weightQ (levels C L) : ℝ) *
        (U : ℝ) ^ (blockFactors E C).card := by
      apply Finset.sum_le_sum
      intro z _
      apply mul_le_mul_of_nonneg_left
      · calc
          _ ≤ |∏ e ∈ blockFactors E C, (sampleQ E query U b C z e : ℝ)| := le_abs_self _
          _ ≤ _ := SmallDegree.abs_product_le _ _ (Nat.cast_nonneg U) (fun e _ => by
            have hr := project_range U hU (Oracle.dyadQ b (query e (localPointQ E C z e) b))
            change |(projectQ U _ : ℝ)| ≤ (U : ℝ)
            rw [abs_of_nonneg (by exact_mod_cast (le_trans (by norm_num : (0 : ℚ) ≤ 1) hr.1))]
            exact_mod_cast hr.2)
      · simp only [CellGrid.weightQ, Rat.cast_inv, Rat.cast_pow, Rat.cast_ofNat]
        positivity
    _ = (U : ℝ) ^ (blockFactors E C).card := by
      rw [← Finset.sum_mul, grid_weights_sum, one_mul]

theorem outputQ_abs_le {n r m Δ : ℕ} (E : FactorFamily n r m)
    (query : (e : Fin m) → (Fin (E e).scope.card → ℚ) → ℕ → ℚ)
    (hdeg : FamilyPrimalDegreeLe E 1) (hocc : FamilyBoundedOccurrence E Δ)
    (U b L : ℕ) (hU : 1 ≤ U) :
    |(outputQ E query U b L : ℝ)| ≤ (U : ℝ) ^ (2 * Δ * n) := by
  unfold outputQ
  push_cast
  have hh := SmallDegree.abs_product_le (blocks E)
    (fun C => (componentEstimateQ E query U b L C : ℝ))
    (by positivity : 0 ≤ (U : ℝ) ^ (2 * Δ)) (fun C hC => by
      rw [abs_of_nonneg (by have h := componentEstimateQ_ge_one E query U b L hU C; linarith)]
      exact (componentEstimateQ_le E query U b L hU C).trans
        (pow_le_pow_right₀ (by exact_mod_cast hU) (blockFactors_card_le E hdeg hocc hC)))
  apply hh.trans
  rw [← pow_mul]
  exact pow_le_pow_right₀ (by exact_mod_cast hU)
    (Nat.mul_le_mul_left _ (blocks_card_le E))

/-- Concrete polynomial bit bound for the reduced numerator and denominator of
the algorithm's actual output. All denominators arise from stored dyadic samples. -/
theorem outputQ_bits_le {n r m Δ : ℕ} (E : FactorFamily n r m)
    (query : (e : Fin m) → (Fin (E e).scope.card → ℚ) → ℕ → ℚ)
    (hdeg : FamilyPrimalDegreeLe E 1) (hocc : FamilyBoundedOccurrence E Δ)
    (U b L : ℕ) (hU : 1 ≤ U) :
    BitComplexity.rationalBits (outputQ E query U b L) ≤
      Nat.clog 2 U * (2 * Δ * n) + 2 * (n * (b * (2 * Δ) + 2 * L)) + 3 := by
  let q := outputQ E query U b L
  let V := n * (b * (2 * Δ) + 2 * L)
  let A := Nat.clog 2 U * (2 * Δ * n)
  have hd : q.den ≤ 2 ^ V := Nat.le_of_dvd (by positivity) (outputQ_den_dvd E query hdeg hocc U b L)
  have hm : |q| ≤ (2 : ℚ) ^ A := by
    have hu := Nat.le_pow_clog (by decide : 1 < 2) U
    have hur : (U : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 U := by exact_mod_cast hu
    have hh := (outputQ_abs_le E query hdeg hocc U b L hU).trans
      (pow_le_pow_left₀ (Nat.cast_nonneg U) hur (2 * Δ * n))
    rw [← pow_mul] at hh
    exact_mod_cast hh
  have hn := Moments.rational_num_size_le_of_abs_den_le q A V hm hd
  have hden : q.den.size ≤ V + 1 := by
    apply Nat.size_le.mpr
    rw [pow_succ]
    have hp : 0 < 2 ^ V := by positivity
    omega
  unfold BitComplexity.rationalBits
  change q.num.natAbs.size + q.den.size + 1 ≤ _
  omega

/-- Every query coordinate is a dyadic with at most the selected mesh precision. -/
theorem localPointQ_isDyadicAt {n r m L : ℕ} (E : FactorFamily n r m) (C : Finset (Fin n))
    (z : CellGrid.Grid (levels C L)) (e : Fin m) (j : Fin (E e).scope.card) :
    IsDyadicAt L (localPointQ E C z e j) := by
  apply IsDyadicAt.mono (P := levels C L ((E e).scope.orderEmbOfFin rfl j))
  · exact ⟨((z ((E e).scope.orderEmbOfFin rfl j)).val : ℤ), by simp [localPointQ, CellGrid.cornerQ]⟩
  · unfold levels
    split_ifs <;> omega

/-- Fixed certified integer upper bounds depending only on the lemma's fixed parameters. -/
def rangeBound (U : ℝ) : ℕ := max 2 ⌈U⌉₊

def lipBudget (Δ : ℕ) (K U : ℝ) : ℕ :=
  ⌈(2 * Δ : ℕ) * K * (rangeBound U : ℝ) ^ (2 * Δ - 1)⌉₊

/-- Lemma A.1 under its original range and Lipschitz hypotheses, with no
zero-free assumption and no component certificate. -/
theorem lemma_A1_accuracy {n r m Δ : ℕ} (E : FactorFamily n r m)
    (O : (e : Fin m) → Oracle.Oracle (E e).scope.card (E e).psi.toFun)
    (hdeg : FamilyPrimalDegreeLe E 1) (hocc : FamilyBoundedOccurrence E Δ)
    {U K : ℝ} (hU : 1 < U) (hK : 0 < K) (hn : 0 < n)
    (hrange : ∀ e x, x ∈ cube (E e).scope.card →
      1 ≤ (E e).psi.toFun x ∧ (E e).psi.toFun x ≤ U)
    (hLip : ∀ e, (E e).LipOk K) (ε : ℚ) (hε : 0 < ε) :
    FPTAS.Accurate
      (runQ E (fun e => (O e).query) Δ (rangeBound U) (lipBudget Δ K U) ε : ℝ)
      (partitionFunctionFactor E) ε := by
  have hUb : U ≤ (rangeBound U : ℝ) := (Nat.le_ceil U).trans (by exact_mod_cast le_max_right 2 ⌈U⌉₊)
  exact runQ_accurate E O hdeg hocc _ _ (by unfold rangeBound; omega) hn hK.le
    (fun e x hx => ⟨(hrange e x hx).1, (hrange e x hx).2.trans hUb⟩) hLip
    (Nat.le_ceil _) ε hε

/-- The `η = 1` branch of Corollary 1.3 uses the direct component algorithm. -/
theorem corollary_1_3_eta_one {n r m Δ : ℕ} (E : FactorFamily n r m)
    (O : (e : Fin m) → Oracle.Oracle (E e).scope.card (E e).psi.toFun)
    (hdeg : FamilyPrimalDegreeLe E 1) (hocc : FamilyBoundedOccurrence E Δ)
    {δ K : ℝ} (hρ : 1 < FPTAS.gamarnikSmediraRho Δ 1 δ) (hK : 0 < K) (hn : 0 < n)
    (hrange : ∀ e x, x ∈ cube (E e).scope.card →
      1 ≤ (E e).psi.toFun x ∧ (E e).psi.toFun x ≤ FPTAS.gamarnikSmediraRho Δ 1 δ)
    (hLip : ∀ e, (E e).LipOk K) (ε : ℚ) (hε : 0 < ε) :
    FPTAS.Accurate
      (runQ E (fun e => (O e).query) Δ (rangeBound (FPTAS.gamarnikSmediraRho Δ 1 δ))
        (lipBudget Δ K (FPTAS.gamarnikSmediraRho Δ 1 δ)) ε : ℝ)
      (partitionFunctionFactor E) ε :=
  lemma_A1_accuracy E O hdeg hocc hρ hK hn hrange hLip ε hε

lemma rationalBits_of_dyadic {q : ℚ} {A V : ℕ} (hq : IsDyadicAt V q)
    (habs : |(q : ℝ)| ≤ (2 : ℝ) ^ A) : BitComplexity.rationalBits q ≤ A + 2 * V + 3 := by
  have hd : q.den ≤ 2 ^ V := Nat.le_of_dvd (by positivity) hq.den_dvd
  have habsq : |q| ≤ (2 : ℚ) ^ A := by exact_mod_cast habs
  have hn := Moments.rational_num_size_le_of_abs_den_le q A V habsq hd
  have hs : q.den.size ≤ V + 1 := by
    apply Nat.size_le.mpr
    rw [pow_succ]
    have hp : 0 < 2 ^ V := by positivity
    omega
  unfold BitComplexity.rationalBits
  omega

theorem localPointQ_bits_le {n r m L : ℕ} (E : FactorFamily n r m) (C : Finset (Fin n))
    (z : CellGrid.Grid (levels C L)) (e : Fin m) (j : Fin (E e).scope.card) :
    BitComplexity.rationalBits (localPointQ E C z e j) ≤ 2 * L + 3 := by
  have h := localPointQ_mem E C z e j
  have hr : (0 : ℝ) ≤ (localPointQ E C z e j : ℝ) ∧ (localPointQ E C z e j : ℝ) ≤ 1 := by
    exact_mod_cast h
  have habs : |(localPointQ E C z e j : ℝ)| ≤ (2 : ℝ) ^ 0 := by
    simpa only [pow_zero, abs_of_nonneg hr.1] using hr.2
  simpa only [Nat.zero_add] using rationalBits_of_dyadic (localPointQ_isDyadicAt E C z e j) habs

/-- A weighted sample term in one component's rational summation. -/
def cellValueQ {n r m L : ℕ} (E : FactorFamily n r m)
    (query : (e : Fin m) → (Fin (E e).scope.card → ℚ) → ℕ → ℚ)
    (U b : ℕ) (C : Finset (Fin n)) (z : CellGrid.Grid (levels C L)) : ℚ :=
  CellGrid.weightQ (levels C L) * ∏ e ∈ blockFactors E C, sampleQ E query U b C z e

lemma cellValueQ_isDyadicAt {n r m L : ℕ} (E : FactorFamily n r m)
    (query : (e : Fin m) → (Fin (E e).scope.card → ℚ) → ℕ → ℚ)
    (U b : ℕ) (C : Finset (Fin n)) (z : CellGrid.Grid (levels C L)) :
    IsDyadicAt (b * (blockFactors E C).card + L * C.card) (cellValueQ E query U b C z) := by
  have hp := IsDyadicAt.prod (blockFactors E C) (sampleQ E query U b C z) b
    (fun e _ => sampleQ_isDyadicAt E query U b C z e)
  have hh := (isDyadicAt_inv_two_pow (∑ v, levels C L v)).mul hp
  unfold cellValueQ CellGrid.weightQ
  convert hh using 1 <;> rw [sum_levels] <;> ring

/-- Every partial component sum, regardless of accumulation order, obeys a
polynomial reduced-rational size bound. -/
theorem partial_component_bits_le {n r m Δ L : ℕ} (E : FactorFamily n r m)
    (query : (e : Fin m) → (Fin (E e).scope.card → ℚ) → ℕ → ℚ)
    (hdeg : FamilyPrimalDegreeLe E 1) (hocc : FamilyBoundedOccurrence E Δ)
    (U b : ℕ) (hU : 1 ≤ U) {C : Finset (Fin n)} (hC : C ∈ blocks E)
    (S : Finset (CellGrid.Grid (levels C L))) :
    BitComplexity.rationalBits (∑ z ∈ S, cellValueQ E query U b C z) ≤
      Nat.clog 2 U * (2 * Δ) + 2 * (b * (2 * Δ) + 2 * L) + 3 := by
  have ht := blockFactors_card_le E hdeg hocc hC
  have hc := block_card_le_two E hdeg hC
  have hdy : IsDyadicAt (b * (2 * Δ) + 2 * L) (∑ z ∈ S, cellValueQ E query U b C z) := by
    exact IsDyadicAt.sum S _ _ (fun z _ => (cellValueQ_isDyadicAt E query U b C z).mono (by nlinarith))
  apply rationalBits_of_dyadic hdy
  have hnonneg (z : CellGrid.Grid (levels C L)) : (0 : ℚ) ≤ cellValueQ E query U b C z := by
    apply mul_nonneg
    · unfold CellGrid.weightQ; positivity
    · exact Finset.prod_nonneg (fun e _ => (by
        change 0 ≤ projectQ U _
        exact le_trans (by norm_num) (project_range U hU _).1))
  have hpnonneg : (0 : ℚ) ≤ ∑ z ∈ S, cellValueQ E query U b C z :=
    Finset.sum_nonneg (fun z _ => hnonneg z)
  have hple : (∑ z ∈ S, cellValueQ E query U b C z) ≤ componentEstimateQ E query U b L C :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun z _ _ => hnonneg z)
  have hr : |((∑ z ∈ S, cellValueQ E query U b C z : ℚ) : ℝ)| ≤
      (U : ℝ) ^ (2 * Δ) := by
    rw [abs_of_nonneg (by exact_mod_cast hpnonneg)]
    have hpr : ((∑ z ∈ S, cellValueQ E query U b C z : ℚ) : ℝ) ≤
        (componentEstimateQ E query U b L C : ℝ) := by exact_mod_cast hple
    exact hpr.trans ((componentEstimateQ_le E query U b L hU C).trans
      (pow_le_pow_right₀ (by exact_mod_cast hU) ht))
  have hu : (U : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 U := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) U
  apply hr.trans
  simpa only [← pow_mul] using pow_le_pow_left₀ (Nat.cast_nonneg U) hu (2 * Δ)

/-- The empty-variable input is handled exactly, including its arbitrary
well-typed labelled factor family. -/
theorem runQ_zero {r m : ℕ} (E : FactorFamily 0 r m)
    (query : (e : Fin m) → (Fin (E e).scope.card → ℚ) → ℕ → ℚ)
    (Δ U T : ℕ) (ε : ℚ) : runQ E query Δ U T ε = 1 := by
  simp [runQ, outputQ, blocks]

theorem partitionFunction_zero {r m : ℕ} (E : FactorFamily 0 r m) : partitionFunctionFactor E = 1 := by
  rw [partitionFunction_eq_prod_blocks E (fun v => Fin.elim0 v)]
  simp [blocks]

/-- The original Lemma A.1 accuracy assertion also includes `n = 0`. -/
theorem lemma_A1_accuracy_all {n r m Δ : ℕ} (E : FactorFamily n r m)
    (O : (e : Fin m) → Oracle.Oracle (E e).scope.card (E e).psi.toFun)
    (hdeg : FamilyPrimalDegreeLe E 1) (hocc : FamilyBoundedOccurrence E Δ)
    {U K : ℝ} (hU : 1 < U) (hK : 0 < K)
    (hrange : ∀ e x, x ∈ cube (E e).scope.card →
      1 ≤ (E e).psi.toFun x ∧ (E e).psi.toFun x ≤ U)
    (hLip : ∀ e, (E e).LipOk K) (ε : ℚ) (hε : 0 < ε) :
    FPTAS.Accurate
      (runQ E (fun e => (O e).query) Δ (rangeBound U) (lipBudget Δ K U) ε : ℝ)
      (partitionFunctionFactor E) ε := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst n
    rw [runQ_zero, partitionFunction_zero]
    exact ⟨by norm_num, by norm_num, by simpa using (show (0 : ℝ) ≤ ε by exact_mod_cast hε.le)⟩
  · exact lemma_A1_accuracy E O hdeg hocc hU hK hn hrange hLip ε hε

/-- Partial products of the rounded factor values also stay short. -/
theorem partial_factor_product_bits_le {n r m Δ L : ℕ} (E : FactorFamily n r m)
    (query : (e : Fin m) → (Fin (E e).scope.card → ℚ) → ℕ → ℚ)
    (hdeg : FamilyPrimalDegreeLe E 1) (hocc : FamilyBoundedOccurrence E Δ)
    (U b : ℕ) (hU : 1 ≤ U) {C : Finset (Fin n)} (hC : C ∈ blocks E)
    (z : CellGrid.Grid (levels C L)) (S : Finset (Fin m)) (hS : S ⊆ blockFactors E C) :
    BitComplexity.rationalBits (∏ e ∈ S, sampleQ E query U b C z e) ≤
      Nat.clog 2 U * (2 * Δ) + 2 * (b * (2 * Δ)) + 3 := by
  have ht : S.card ≤ 2 * Δ := (Finset.card_le_card hS).trans (blockFactors_card_le E hdeg hocc hC)
  have hd := (IsDyadicAt.prod S (sampleQ E query U b C z) b
    (fun e _ => sampleQ_isDyadicAt E query U b C z e)).mono (Nat.mul_le_mul_left b ht)
  apply rationalBits_of_dyadic hd
  push_cast
  have hh := SmallDegree.abs_product_le S (fun e => (sampleQ E query U b C z e : ℝ))
    (Nat.cast_nonneg U) (fun e _ => by
      have hr := project_range U hU (Oracle.dyadQ b (query e (localPointQ E C z e) b))
      change |(projectQ U _ : ℝ)| ≤ (U : ℝ)
      rw [abs_of_nonneg (by exact_mod_cast (le_trans (by norm_num : (0 : ℚ) ≤ 1) hr.1))]
      exact_mod_cast hr.2)
  have hu : (U : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 U := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) U
  apply (hh.trans (pow_le_pow_right₀ (by exact_mod_cast hU) ht)).trans
  simpa only [← pow_mul] using pow_le_pow_left₀ (Nat.cast_nonneg U) hu (2 * Δ)

/-- Any partial final component product has the same global polynomial bit bound. -/
theorem partial_output_bits_le {n r m Δ : ℕ} (E : FactorFamily n r m)
    (query : (e : Fin m) → (Fin (E e).scope.card → ℚ) → ℕ → ℚ)
    (hdeg : FamilyPrimalDegreeLe E 1) (hocc : FamilyBoundedOccurrence E Δ)
    (U b L : ℕ) (hU : 1 ≤ U) (S : Finset (Finset (Fin n))) (hS : S ⊆ blocks E) :
    BitComplexity.rationalBits (∏ C ∈ S, componentEstimateQ E query U b L C) ≤
      Nat.clog 2 U * (2 * Δ * n) + 2 * (n * (b * (2 * Δ) + 2 * L)) + 3 := by
  have hcard : S.card ≤ n := (Finset.card_le_card hS).trans (blocks_card_le E)
  have hd := IsDyadicAt.prod S (componentEstimateQ E query U b L) (b * (2 * Δ) + 2 * L)
    (fun C hC => (componentEstimateQ_isDyadicAt E query U b L C).mono (by
      have ht := blockFactors_card_le E hdeg hocc (hS hC)
      have hc := block_card_le_two E hdeg (hS hC)
      nlinarith))
  have hd' := hd.mono (show (b * (2 * Δ) + 2 * L) * S.card ≤ n * (b * (2 * Δ) + 2 * L) by
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_left (b * (2 * Δ) + 2 * L) hcard)
  apply rationalBits_of_dyadic hd'
  push_cast
  have hh := SmallDegree.abs_product_le S
    (fun C => (componentEstimateQ E query U b L C : ℝ)) (by positivity : 0 ≤ (U : ℝ) ^ (2 * Δ))
    (fun C hC => by
      rw [abs_of_nonneg (by have h := componentEstimateQ_ge_one E query U b L hU C; linarith)]
      exact (componentEstimateQ_le E query U b L hU C).trans
        (pow_le_pow_right₀ (by exact_mod_cast hU) (blockFactors_card_le E hdeg hocc (hS hC))))
  have hu : (U : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 U := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) U
  rw [← pow_mul] at hh
  apply (hh.trans (pow_le_pow_right₀ (by exact_mod_cast hU) (Nat.mul_le_mul_left (2 * Δ) hcard))).trans
  simpa only [← pow_mul] using pow_le_pow_left₀ (Nat.cast_nonneg U) hu (2 * Δ * n)

/-- The degree-one corollary includes the empty-variable instance. -/
theorem corollary_1_3_eta_one_all {n r m Δ : ℕ} (E : FactorFamily n r m)
    (O : (e : Fin m) → Oracle.Oracle (E e).scope.card (E e).psi.toFun)
    (hdeg : FamilyPrimalDegreeLe E 1) (hocc : FamilyBoundedOccurrence E Δ)
    {δ K : ℝ} (hρ : 1 < FPTAS.gamarnikSmediraRho Δ 1 δ) (hK : 0 < K)
    (hrange : ∀ e x, x ∈ cube (E e).scope.card →
      1 ≤ (E e).psi.toFun x ∧ (E e).psi.toFun x ≤ FPTAS.gamarnikSmediraRho Δ 1 δ)
    (hLip : ∀ e, (E e).LipOk K) (ε : ℚ) (hε : 0 < ε) :
    FPTAS.Accurate
      (runQ E (fun e => (O e).query) Δ (rangeBound (FPTAS.gamarnikSmediraRho Δ 1 δ))
        (lipBudget Δ K (FPTAS.gamarnikSmediraRho Δ 1 δ)) ε : ℝ)
      (partitionFunctionFactor E) ε :=
  lemma_A1_accuracy_all E O hdeg hocc hρ hK hrange hLip ε hε

end Paper08.LowDegreeAlgorithm
