/-
Copyright (c) 2026. Actual random-color kernels and their contraction estimates.
-/
import Paper09.Coupling
import Paper09.Markov
import Paper09.BlockColoring
import Paper09.Main

open Finset BigOperators Classical Real
noncomputable section
set_option maxHeartbeats 800000
set_option maxRecDepth 4000

namespace Paper09.BlockDynamics

local instance (priority := 2000) blockSiteDecEq {d n : ℕ} :
    DecidableEq ↥(Paper09.BlockCovering.volume (d := d) n) := Classical.decEq _

section Mixtures
variable {ι α : Type*} [Fintype ι] [Nonempty ι] [Fintype α]

/-- Uniform choice of a color, followed by the selected actual kernel row. -/
def average (p : ι → FinProb α) : FinProb α where
  w x := (∑ i, (p i).w x) / Fintype.card ι
  nonneg x := div_nonneg (sum_nonneg fun i _ => (p i).nonneg x) (Nat.cast_nonneg _)
  sum_one := by
    rw [← sum_div, sum_comm]
    simp only [FinProb.sum_one, sum_const, card_univ, nsmul_eq_mul, mul_one]
    exact div_self (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

/-- Average actual couplings using the same selected color in both chains. -/
def averageCoupling {p q : ι → FinProb α} (c : ∀ i, Coupling (p i) (q i)) :
    Coupling (average p) (average q) where
  mass x y := (∑ i, (c i).mass x y) / Fintype.card ι
  nonneg x y := div_nonneg (sum_nonneg fun i _ => (c i).nonneg x y) (Nat.cast_nonneg _)
  row x := by
    change (∑ y, (∑ i, (c i).mass x y) / _) = _
    rw [← sum_div, sum_comm]
    simp only [Coupling.row, average]
  col y := by
    change (∑ x, (∑ i, (c i).mass x y) / _) = _
    rw [← sum_div, sum_comm]
    simp only [Coupling.col, average]

theorem averageCoupling_cost {p q : ι → FinProb α}
    (c : ∀ i, Coupling (p i) (q i)) (D : α → α → ℝ) :
    (averageCoupling c).cost D = (∑ i, (c i).cost D) / Fintype.card ι := by
  unfold Coupling.cost averageCoupling
  simp only [div_mul_eq_mul_div, sum_mul, ← sum_div]
  congr 1
  calc
    (∑ x, ∑ y, ∑ i, (c i).mass x y * D x y) =
        ∑ x, ∑ i, ∑ y, (c i).mass x y * D x y := by
      apply sum_congr rfl
      intro x _
      rw [sum_comm]
    _ = _ := sum_comm

/-- Convexity follows from real couplings and an epsilon-infimum argument. -/
theorem wasserstein_average_le (D : α → α → ℝ) (hD : ∀ x y, 0 ≤ D x y)
    (p q : ι → FinProb α) :
    wasserstein D (average p) (average q) ≤
      (∑ i, wasserstein D (p i) (q i)) / Fintype.card ι := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hchoices : ∀ i, ∃ c : Coupling (p i) (q i),
      c.cost D < wasserstein D (p i) (q i) + ε :=
    fun i => Wasserstein.exists_cost_lt (p i) (q i) D hε
  choose c hc using hchoices
  have hcard : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  calc
    wasserstein D (average p) (average q) ≤ (averageCoupling c).cost D :=
      Wasserstein.le_cost hD _
    _ = (∑ i, (c i).cost D) / Fintype.card ι := averageCoupling_cost c D
    _ ≤ (∑ i, (wasserstein D (p i) (q i) + ε)) / Fintype.card ι :=
      div_le_div_of_nonneg_right (sum_le_sum fun i _ => (hc i).le) hcard.le
    _ = (∑ i, wasserstein D (p i) (q i)) / Fintype.card ι + ε := by
      rw [sum_add_distrib]
      simp only [sum_const, card_univ, nsmul_eq_mul]
      field_simp

/-- The random-color transition law. -/
def colorKernel (K : ι → α → FinProb α) (x : α) : FinProb α := average (fun i => K i x)

/-- Every color preserving the Gibbs law implies preservation by the sampled
color kernel; this is a statement about the actual probability weights. -/
theorem colorKernel_stationary (K : ι → α → FinProb α) (p : FinProb α)
    (hK : ∀ i, p.bind (K i) = p) : p.bind (colorKernel K) = p := by
  have hw (i : ι) (y : α) : ∑ x, p.w x * (K i x).w y = p.w y :=
    congrArg (fun r : FinProb α => r.w y) (hK i)
  have he : (p.bind (colorKernel K)).w = p.w := by
    funext y
    change (∑ x, p.w x * ((∑ i, (K i x).w y) / _)) = _
    simp only [mul_div, mul_sum, ← sum_div]
    rw [sum_comm]
    simp only [hw, sum_const, card_univ, nsmul_eq_mul]
    exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  cases h : p.bind (colorKernel K) with
  | mk w hw hs =>
    cases p with
    | mk v hv ht =>
      simp only [h] at he
      cases he
      rfl

end Mixtures

section Counting
variable {V ι : Type*} [Fintype V] [Fintype ι]

/-- Per-color one-discrepancy budget: updates containing the discrepancy erase
it, while boundary-adjacent updates create only the proved influence cost. -/
def stepBudget {Q : ℕ} (c : ι → Fin Q) (B D : ι → Finset V)
    (H : ℝ) (a : Fin Q) (y : V) : ℝ :=
  1 - (∑ i, if c i = a ∧ y ∈ B i then (1 : ℝ) else 0) +
    H * (∑ i, if c i = a ∧ y ∈ D i then (1 : ℝ) else 0)

theorem sum_color_indicator {Q : ℕ} (c : ι → Fin Q) (B : ι → Finset V) (y : V) :
    (∑ a : Fin Q, ∑ i, if c i = a ∧ y ∈ B i then (1 : ℝ) else 0) =
      (Finset.univ.filter (fun i => y ∈ B i)).card := by
  rw [sum_comm]
  simp only [ite_and]
  simp [Finset.sum_boole, eq_comm]

theorem sum_stepBudget {Q : ℕ} (c : ι → Fin Q) (B D : ι → Finset V)
    (H : ℝ) (y : V) :
    (∑ a : Fin Q, stepBudget c B D H a y) =
      Q - (Finset.univ.filter (fun i => y ∈ B i)).card +
        H * (Finset.univ.filter (fun i => y ∈ D i)).card := by
  simp only [stepBudget, sum_add_distrib, sum_sub_distrib, ← mul_sum]
  rw [sum_color_indicator, sum_color_indicator]
  simp

/-- Averaging the actual color laws gives the full one-discrepancy contraction
(3.15) once the per-color Gibbs coupling estimates have been established. -/
theorem colorKernel_one_site {Q : ℕ} [NeZero Q] (hQ : 0 < Q)
    (c : ι → Fin Q) (B D : ι → Finset V) (H : ℝ)
    (K : Fin Q → Config V → FinProb (Config V)) (η ξ : Config V) (y : V)
    (hclass : ∀ a, hammingWasserstein (K a η) (K a ξ) ≤ stepBudget c B D H a y) :
    hammingWasserstein (colorKernel K η) (colorKernel K ξ) ≤
      1 - ((Finset.univ.filter (fun i => y ∈ B i)).card : ℝ) / Q +
        H * ((Finset.univ.filter (fun i => y ∈ D i)).card : ℝ) / Q := by
  letI : Nonempty (Fin Q) := ⟨⟨0,hQ⟩⟩
  have hc : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
  calc
    hammingWasserstein (colorKernel K η) (colorKernel K ξ) ≤
        (∑ a : Fin Q, hammingWasserstein (K a η) (K a ξ)) / Q := by
      simpa [colorKernel, hammingWasserstein] using
        wasserstein_average_le hammingR hammingR_nonneg (fun a => K a η) (fun a => K a ξ)
    _ ≤ (∑ a : Fin Q, stepBudget c B D H a y) / Q :=
      div_le_div_of_nonneg_right (sum_le_sum fun a _ => hclass a) hc.le
    _ = _ := by rw [sum_stepBudget]; field_simp

/-- The simulation cost is charged only to the affected color. Averaging
retains the source factor `(I+J)/Q`, rather than charging every block. -/
theorem simulated_colorKernel_one_site {Q : ℕ} [NeZero Q] (hQ : 0 < Q)
    (c : ι → Fin Q) (B D : ι → Finset V) (H E : ℝ)
    (K : Fin Q → Config V → FinProb (Config V)) (η ξ : Config V) (y : V)
    (hclass : ∀ a, hammingWasserstein (K a η) (K a ξ) ≤ stepBudget c B D H a y +
      E * ((∑ i, if c i = a ∧ y ∈ B i then (1:ℝ) else 0) +
        (∑ i, if c i = a ∧ y ∈ D i then (1:ℝ) else 0))) :
    hammingWasserstein (colorKernel K η) (colorKernel K ξ) ≤
      1 - ((univ.filter (fun i => y ∈ B i)).card : ℝ)/Q +
        H*((univ.filter (fun i => y ∈ D i)).card : ℝ)/Q +
        E*(((univ.filter (fun i => y ∈ B i)).card : ℝ) +
          ((univ.filter (fun i => y ∈ D i)).card : ℝ))/Q := by
  have hc : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
  calc
    hammingWasserstein (colorKernel K η) (colorKernel K ξ) ≤
        (∑ a : Fin Q, hammingWasserstein (K a η) (K a ξ)) / Q := by
      simpa [colorKernel,hammingWasserstein] using
        wasserstein_average_le hammingR hammingR_nonneg (fun a => K a η) (fun a => K a ξ)
    _ ≤ (∑ a : Fin Q, (stepBudget c B D H a y +
        E * ((∑ i, if c i = a ∧ y ∈ B i then (1:ℝ) else 0) +
          (∑ i, if c i = a ∧ y ∈ D i then (1:ℝ) else 0)))) / Q :=
      div_le_div_of_nonneg_right (sum_le_sum fun a _ => hclass a) hc.le
    _ = _ := by
      rw [sum_add_distrib, sum_stepBudget, ← mul_sum, sum_add_distrib,
        sum_color_indicator, sum_color_indicator]
      field_simp
      <;> ring

/-- Once the proved influence and local simulation error have been inserted,
(3.19) follows with the explicit remaining incidence gain. -/
theorem simulated_budget_absorbed (I J Q H M cstar : ℝ)
    (hI : 0 < I) (hJ : 0 ≤ J) (hQ : 0 < Q) (hM : 1 ≤ M)
    (hc : 0 < cstar) (hcsmall : cstar ≤ 1/32)
    (hH : 0 ≤ H) (hHJ : H*J ≤ I/2) (hIJ : I+J ≤ 4*I) :
    1-I/Q+H*J/Q+2*M*(cstar/M^2)*(I+J)/Q ≤ 1-I/(4*Q) := by
  have hfirst := ideal_step_one_site I J Q H hI hQ hJ hH hHJ
  have herr := simulated_error_absorbed M I J Q cstar hM hI hQ hJ hc hcsmall hIJ
  have heq : I/(2*Q)-I/(4*Q)=I/(4*Q) := by field_simp; ring
  linarith

end Counting

open Paper09.BlockCovering Paper09.BlockColoring Paper09.LatticeGeometry

/-- The exact physical sites of an indexed covering block, in the finite
spin space used by the RFIM kernels. -/
def blockSites {d : ℕ} {good : Point d → Prop} {n s : ℕ}
    (i : BlockIndex good n s) : Finset ↥(volume (d := d) n) :=
  univ.filter (fun x => x.val ∈ block i)

def boundarySites {d : ℕ} {good : Point d → Prop} {n s : ℕ}
    (i : BlockIndex good n s) : Finset ↥(volume (d := d) n) :=
  univ.filter (fun x => x.val ∈ boundary (volume (d := d) n) (block i))

@[simp] theorem mem_blockSites {d : ℕ} {good : Point d → Prop} {n s : ℕ}
    (i : BlockIndex good n s) (x : ↥(volume (d := d) n)) : x ∈ blockSites i ↔ x.val ∈ block i := by
  simp [blockSites]

@[simp] theorem mem_boundarySites {d : ℕ} {good : Point d → Prop} {n s : ℕ}
    (i : BlockIndex good n s) (x : ↥(volume (d := d) n)) :
    x ∈ boundarySites i ↔ x.val ∈ boundary (volume (d := d) n) (block i) := by
  simp [boundarySites]

/-- The actual block incidence counts agree before and after passing to the
finite-domain site type. -/
theorem blockSites_count {d : ℕ} (good : Point d → Prop) (n s : ℕ) (y : ↥(volume (d := d) n)) :
    (univ.filter (fun i : BlockIndex good n s => y ∈ blockSites i)).card = I good n s y.val := by
  simpa only [mem_blockSites] using card_block_cover good n s y.val

theorem boundarySites_count {d : ℕ} (good : Point d → Prop) (n s : ℕ) (y : ↥(volume (d := d) n)) :
    (univ.filter (fun i : BlockIndex good n s => y ∈ boundarySites i)).card = J good n s y.val := by
  simpa only [mem_boundarySites] using card_block_boundary good n s y.val

/-- Explicit dimension-only contraction coefficient. -/
def coveringRate (d : ℕ) : ℝ := 1 / (4 * (4 : ℝ)^d * coloringConstant d)

theorem coveringRate_pos (d : ℕ) : 0 < coveringRate d := by
  unfold coveringRate coloringConstant
  positivity

private theorem incidence_ratio_lower (F D M R Q I : ℝ)
    (hF : 0 < F) (hD : 0 < D) (hM : 0 < M) (hR : 0 ≤ R)
    (hQ : 0 < Q) (hinc : R ≤ F*I) (hpalette : Q ≤ D*M*R) :
    (1/(4*F*D))/M ≤ I/(4*Q) := by
  rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have hh := mul_le_mul_of_nonneg_left hinc (mul_nonneg hD.le hM.le)
  nlinarith only [hh,hpalette]

/-- The covering and the constructed coloring give the original uniform
`c/M` incidence ratio; there is no assumed overlap or color-count certificate. -/
theorem covering_incidence_ratio {d : ℕ} {good : Point d → Prop} {n s L : ℕ}
    (hs : 0 < s) (hevent : SmallClusters good n s L) (y : ↥(volume (d := d) n)) :
    coveringRate d / maxBlockSize good n s ≤
      (I good n s y.val : ℝ) / (4 * colorCount good n s) := by
  have hQn := colorCount_pos hs hevent
  have hQ : (0 : ℝ) < colorCount good n s := Nat.cast_pos.mpr hQn
  have hM : 0 < maxBlockSize good n s := by
    by_contra hn
    have hz : maxBlockSize good n s = 0 := by omega
    simp [colorCount,hz] at hQn
  have hI := (covering_scaled hs hevent y.property).1
  have hI' : ((8*s)^d : ℝ) ≤ (4:ℝ)^d * I good n s y.val := by exact_mod_cast hI
  have hD : (0 : ℝ) < coloringConstant d := by unfold coloringConstant; positivity
  have hp : (colorCount good n s : ℝ) ≤
      (coloringConstant d : ℝ) * maxBlockSize good n s * ((8*s)^d : ℝ) := by
    simp only [colorCount,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    exact le_rfl
  exact incidence_ratio_lower _ _ _ _ _ _ (by positivity) hD
    (Nat.cast_pos.mpr hM) (by positivity) hQ hI' hp

/-- Equation (3.15) for a fixed actual covering and its proper coloring.
The per-color hypotheses are the local Gibbs influence estimates; all
incidence counts and the random-color averaging are proved here. -/
theorem covering_color_one_site {d : ℕ} {good : Point d → Prop} {n s L Q : ℕ}
    [NeZero Q] (hQ : 0 < Q) (hs : 0 < s) (hevent : SmallClusters good n s L)
    (c : (conflictGraph good n s).Coloring (Fin Q)) (H : ℝ)
    (K : Fin Q → Config ↥(volume (d := d) n) → FinProb (Config ↥(volume (d := d) n)))
    (η ξ : Config ↥(volume (d := d) n)) (y : ↥(volume (d := d) n))
    (hclass : ∀ a, hammingWasserstein (K a η) (K a ξ) ≤
      stepBudget (V := ↥(volume (d := d) n)) (ι := BlockIndex good n s)
        (fun i => c i) (fun i => blockSites i) (fun i => boundarySites i) H a y) :
    hammingWasserstein (colorKernel K η) (colorKernel K ξ) ≤
      1 - (I good n s y.val : ℝ)/Q + H*(J good n s y.val : ℝ)/Q := by
  simpa only [blockSites_count,boundarySites_count] using
    colorKernel_one_site hQ (fun i => c i) (fun i => blockSites i) (fun i => boundarySites i) H K η ξ y hclass

end Paper09.BlockDynamics
