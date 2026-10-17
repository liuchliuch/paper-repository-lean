import Paper22.Divergences
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Extended-real meaning of the reliability quantities

The formulas in `Divergences` are real-valued in the full-rank range used by
Theorem 2. This module defines the source's extended-real quantities without
using the convention `log 0 = 0`, and proves their agreement with those real
formulas when every channel output is positive definite.
-/

open scoped MatrixOrder ComplexOrder
open Matrix
noncomputable section
namespace Paper22
variable {n d : ℕ}

/-- The source sums only over letters of strictly positive input probability. -/
def orderAlphaObjExtended (α : ℝ) (V : CQChannel n d) (q : Fin n → ℝ)
    (σ : Matrix (Fin d) (Fin d) ℂ) : EReal :=
  ∑ x, if 0 < q x then (q x : EReal) * petzRenyi α (V.states x) σ else 0

/-- Extended-real infimum over all density reference states. -/
def orderAlphaInfExtended (α : ℝ) (V : CQChannel n d) (q : Fin n → ℝ) : EReal :=
  sInf {s | ∃ σ, IsDensity σ ∧ s = orderAlphaObjExtended α V q σ}

/-- Equation (5), with an extended-real inner infimum and outer supremum. -/
def orderAlphaCapacityExtended (V : CQChannel n d) (α : ℝ) : EReal :=
  sSup {t | ∃ q : Fin n → ℝ, (∀ i, 0 ≤ q i) ∧ (∑ i, q i = 1) ∧
    t = orderAlphaInfExtended α V q}

/-- The endpoint `α = 1` contributes zero exactly as in equation (6). -/
def spherePackingTermExtended (V : CQChannel n d) (α R : ℝ) : EReal :=
  if α = 1 then 0 else
    if 0 < α ∧ α < 1 then
      (((1 - α) / α : ℝ) : EReal) * (orderAlphaCapacityExtended V α - (R : EReal))
    else 0

/-- Extended-real sphere packing; valid also for singular outputs or negative rates. -/
def spherePackingExtended (V : CQChannel n d) (R : ℝ) : EReal :=
  sSup ((fun α => spherePackingTermExtended V α R) '' Set.Ioc 0 1)

lemma divergence_coe_sum (f : Fin n → ℝ) :
    ((∑ x, f x : ℝ) : EReal) = ∑ x, (f x : EReal) := by
  classical
  exact map_sum (⟨⟨fun x : ℝ => (x : EReal), EReal.coe_zero⟩, EReal.coe_add⟩ : ℝ →+ EReal) f _

lemma orderAlphaObjExtended_eq_coe (V : CQChannel n d) (hV : V.FullRank)
    {α : ℝ} (hα : α ∈ Set.Ioo 0 1) {q : Fin n → ℝ} (hq : ∀ x, 0 ≤ q x)
    {σ : Matrix (Fin d) (Fin d) ℂ} (hσ : IsDensity σ) :
    orderAlphaObjExtended α V q σ = (orderAlphaObj α V q σ : EReal) := by
  classical
  rw [orderAlphaObj, divergence_coe_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : 0 < q x
  · simp only [orderAlphaObjExtended, hx, if_pos]
    have hp : petzRenyi α (V.states x) σ = (petzRenyiRe α (V.states x) σ : EReal) :=
      petzRenyi_eq_coe_of_fullRank (hV x) hσ hα
    rw [hp, EReal.coe_mul]
  · have hz : q x = 0 := le_antisymm (le_of_not_gt hx) (hq x)
    simp [orderAlphaObjExtended, hx, hz]

/-- Coercion into the extended reals preserves a nonempty, bounded real infimum. -/
lemma divergence_coe_sInf {s : Set ℝ} (hs : s.Nonempty) (hb : BddBelow s) :
    ((sInf s : ℝ) : EReal) = sInf ((fun x : ℝ => (x : EReal)) '' s) := by
  change (((sInf s : ℝ) : WithTop ℝ) : WithBot (WithTop ℝ)) = _
  rw [WithTop.coe_sInf' hs hb,
    WithBot.coe_sInf' (WithTop.coe_mono.map_bddBelow hb)]
  simp only [Set.image_image]
  rfl

/-- Coercion into the extended reals preserves a nonempty, bounded real supremum. -/
lemma divergence_coe_sSup {s : Set ℝ} (hs : s.Nonempty) (hb : BddAbove s) :
    ((sSup s : ℝ) : EReal) = sSup ((fun x : ℝ => (x : EReal)) '' s) := by
  change (((sSup s : ℝ) : WithTop ℝ) : WithBot (WithTop ℝ)) = _
  rw [WithTop.coe_sSup' hb,
    WithBot.coe_sSup' (hs.image ((↑) : ℝ → WithTop ℝ)) (WithTop.coe_mono.map_bddAbove hb)]
  simp only [Set.image_image]
  rfl

lemma orderAlphaInfExtended_eq_coe [NeZero d] (V : CQChannel n d) (hV : V.FullRank)
    {α : ℝ} (hα : α ∈ Set.Ioo 0 1) {q : Fin n → ℝ}
    (hq0 : ∀ x, 0 ≤ q x) (hq1 : ∑ x, q x = 1) :
    orderAlphaInfExtended α V q = (orderAlphaInf α V q : EReal) := by
  unfold orderAlphaInfExtended
  rw [orderAlphaInf, divergence_coe_sInf (orderAlpha_values_nonempty V α q)
    (orderAlpha_values_bddBelow V hα hq0 hq1)]
  congr 1
  ext s
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨orderAlphaObj α V q σ, ⟨σ, hσ, rfl⟩,
      (orderAlphaObjExtended_eq_coe V hV hα hq0 hσ).symm⟩
  · rintro ⟨t, ⟨σ, hσ, rfl⟩, rfl⟩
    exact ⟨σ, hσ, (orderAlphaObjExtended_eq_coe V hV hα hq0 hσ).symm⟩

lemma orderAlphaCapacityExtended_eq_coe [NeZero n] [NeZero d]
    (V : CQChannel n d) (hV : V.FullRank) {α : ℝ} (hα : α ∈ Set.Ioo 0 1) :
    orderAlphaCapacityExtended V α = (orderAlphaCapacity V α : EReal) := by
  obtain ⟨lam, hlam0, hlam⟩ := V.exists_uniform_spectral_lower_bound hV
  have hb : BddAbove {t | ∃ q : Fin n → ℝ, (∀ i, 0 ≤ q i) ∧ (∑ i, q i = 1) ∧
      t = orderAlphaInf α V q} := by
    refine ⟨-α / (1 - α) * log2 ((d : ℝ) * lam), ?_⟩
    intro t ht
    have hle : t ≤ orderAlphaCapacity V α := by
      apply le_csSup ?_ ht
      refine ⟨?_, ?_⟩
      · exact -α / (1 - α) * log2 ((d : ℝ) * lam)
      · intro z hz
        obtain ⟨q, hq0, hq1, rfl⟩ := hz
        have hinf : orderAlphaInf α V q ≤ orderAlphaObj α V q (maximallyMixed d) :=
          csInf_le (orderAlpha_values_bddBelow V hα hq0 hq1)
            ⟨maximallyMixed d, maximallyMixed_isDensity (NeZero.pos d), rfl⟩
        apply hinf.trans
        unfold orderAlphaObj
        calc ∑ x, q x * petzRenyiRe α (V.states x) (maximallyMixed d)
            ≤ ∑ x, q x * (-α / (1 - α) * log2 ((d : ℝ) * lam)) :=
              Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
                (petzRenyiRe_uniform_upper_bound (V.isDensity x).posSemidef
                  (NeZero.pos d) (hlam x) hlam0 hα.1 hα.2) (hq0 x)
          _ = _ := by rw [← Finset.sum_mul, hq1, one_mul]
    exact hle.trans (orderAlphaCapacity_le V (NeZero.pos d) hV hlam hlam0 hα.1 hα.2)
  have hn : Set.Nonempty {t | ∃ q : Fin n → ℝ, (∀ i, 0 ≤ q i) ∧ (∑ i, q i = 1) ∧
      t = orderAlphaInf α V q} := by
    let q := ProbDist.uniform n (NeZero.pos n)
    exact ⟨_, q.q, q.nonneg, q.sum_eq_one, rfl⟩
  unfold orderAlphaCapacityExtended
  rw [orderAlphaCapacity, divergence_coe_sSup hn hb]
  congr 1
  ext t
  constructor
  · rintro ⟨q, hq0, hq1, rfl⟩
    exact ⟨orderAlphaInf α V q, ⟨q, hq0, hq1, rfl⟩,
      (orderAlphaInfExtended_eq_coe V hV hα hq0 hq1).symm⟩
  · rintro ⟨s, ⟨q, hq0, hq1, rfl⟩, rfl⟩
    exact ⟨q, hq0, hq1, (orderAlphaInfExtended_eq_coe V hV hα hq0 hq1).symm⟩

lemma spherePackingTermExtended_eq_coe [NeZero n] [NeZero d]
    (V : CQChannel n d) (hV : V.FullRank) (α R : ℝ) :
    spherePackingTermExtended V α R = (spherePackingTerm V α R : EReal) := by
  unfold spherePackingTermExtended spherePackingTerm
  split_ifs with h1 hα
  · rfl
  · rw [orderAlphaCapacityExtended_eq_coe V hV hα, ← EReal.coe_sub, ← EReal.coe_mul]
  · rfl

/-- On nonnegative rates the real function is exactly the finite extended-real one. -/
lemma spherePackingExtended_eq_coe [NeZero n] [NeZero d]
    (V : CQChannel n d) (hV : V.FullRank) {R : ℝ} (hR : 0 ≤ R) :
    spherePackingExtended V R = (spherePacking V R : EReal) := by
  rw [spherePacking, divergence_coe_sSup ⟨0, spherePackingTerm_one_mem V R⟩
    (spherePacking_bddAbove V hV hR)]
  unfold spherePackingExtended
  congr 1
  ext s
  simp only [Set.mem_image]
  constructor
  · rintro ⟨α, hα, rfl⟩
    exact ⟨spherePackingTerm V α R, ⟨α, hα, rfl⟩,
      (spherePackingTermExtended_eq_coe V hV α R).symm⟩
  · rintro ⟨t, ⟨α, hα, rfl⟩, rfl⟩
    exact ⟨α, hα, spherePackingTermExtended_eq_coe V hV α R⟩

/-- The source's capacity with its separately specified Holevo endpoint.
This definition records `C₁(W) = C(W)`; it does not claim the alpha-to-one limit. -/
def renyiCapacity (V : CQChannel n d) (α : ℝ) : ℝ :=
  if α = 1 then holevoCapacity V else orderAlphaCapacity V α

/-- Extended-real version of the source capacity, with the Holevo endpoint. -/
def renyiCapacityExtended (V : CQChannel n d) (α : ℝ) : EReal :=
  if α = 1 then (holevoCapacity V : EReal) else orderAlphaCapacityExtended V α

@[simp] lemma renyiCapacity_one (V : CQChannel n d) :
    renyiCapacity V 1 = holevoCapacity V := by simp [renyiCapacity]

@[simp] lemma renyiCapacityExtended_one (V : CQChannel n d) :
    renyiCapacityExtended V 1 = (holevoCapacity V : EReal) := by
  simp [renyiCapacityExtended]

lemma renyiCapacity_of_mem_Ioo (V : CQChannel n d) {α : ℝ}
    (hα : α ∈ Set.Ioo 0 1) : renyiCapacity V α = orderAlphaCapacity V α := by
  exact if_neg (ne_of_lt hα.2)

lemma renyiCapacityExtended_of_mem_Ioo (V : CQChannel n d) {α : ℝ}
    (hα : α ∈ Set.Ioo 0 1) :
    renyiCapacityExtended V α = orderAlphaCapacityExtended V α := by
  exact if_neg (ne_of_lt hα.2)

lemma renyiCapacityExtended_eq_coe [NeZero n] [NeZero d]
    (V : CQChannel n d) (hV : V.FullRank) {α : ℝ} (hα : α ∈ Set.Ioc 0 1) :
    renyiCapacityExtended V α = (renyiCapacity V α : EReal) := by
  by_cases h1 : α = 1
  · subst α
    simp
  · have hα' : α ∈ Set.Ioo 0 1 := ⟨hα.1, lt_of_le_of_ne hα.2 h1⟩
    rw [renyiCapacity_of_mem_Ioo V hα', renyiCapacityExtended_of_mem_Ioo V hα']
    exact orderAlphaCapacityExtended_eq_coe V hV hα'

lemma spherePackingTerm_eq_renyiCapacity (V : CQChannel n d) {α : ℝ}
    (hα : α ∈ Set.Ioo 0 1) (R : ℝ) :
    spherePackingTerm V α R = (1 - α) / α * (renyiCapacity V α - R) := by
  rw [renyiCapacity_of_mem_Ioo V hα, spherePackingTerm_of_Ioo V hα]

end Paper22
end
