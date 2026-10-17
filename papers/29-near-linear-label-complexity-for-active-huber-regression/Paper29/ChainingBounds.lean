import Paper29.ProcessTools
import Mathlib.Data.Finite.Card

noncomputable section
open scoped ENNReal
namespace Paper29.Chaining

private theorem top_quotient_subsingleton (T : Type*) :
    Subsingleton (Quotient (⊤ : Setoid T)) := by
  refine ⟨fun x y => ?_⟩
  induction x using Quotient.inductionOn
  induction y using Quotient.inductionOn
  exact Quotient.sound trivial

/-- The indiscrete sequence is always admissible, including the empty space. -/
def indiscrete (T : Type*) : AdmissiblePartitions T where
  cell := fun _ => ⊤
  initial := fun _ _ => trivial
  nested := fun _ _ _ _ => trivial
  finite := fun _ => by
    letI := top_quotient_subsingleton T
    infer_instance
  cardinality := fun _ => by
    letI := top_quotient_subsingleton T
    have hcard : Nat.card (Quotient (⊤ : Setoid T)) ≤ 1 :=
      Finite.card_le_one_iff_subsingleton.mpr inferInstance
    exact hcard.trans (Nat.one_le_pow _ _ (by norm_num))

theorem gamma2_zero (T : Type*) : gamma2 (T := T) (fun _ _ => 0) = 0 := by
  apply le_antisymm _ bot_le
  apply (iInf_le _ (indiscrete T)).trans
  simp [cellDiameter]

/-- Pointwise domination of distances controls every admissible cell diameter. -/
theorem cellDiameter_le_mul {T : Type*} (d e : T → T → ℝ≥0∞)
    (c : ℝ≥0∞) (h : ∀ x y, d x y ≤ c * e x y)
    (P : AdmissiblePartitions T) (k : ℕ) (t : T) :
    cellDiameter d P k t ≤ c * cellDiameter e P k t := by
  apply iSup_le
  intro x
  apply iSup_le
  intro hx
  apply iSup_le
  intro y
  apply iSup_le
  intro hy
  have hyb : e x y ≤ ⨆ (_ : (P.cell k).r t y), e x y :=
    le_iSup (fun _ : (P.cell k).r t y => e x y) hy
  have hyb' : e x y ≤ ⨆ (v : T) (_ : (P.cell k).r t v), e x v :=
    le_iSup_of_le y hyb
  have hxb : e x y ≤ ⨆ (_ : (P.cell k).r t x) (v : T) (_ : (P.cell k).r t v), e x v :=
    le_iSup_of_le hx hyb'
  have hfull : e x y ≤ cellDiameter e P k t := le_iSup_of_le x hxb
  exact (h x y).trans (mul_le_mul_left' hfull c)

/-- Homogeneity/monotonicity of the actual partition functional, proved from
its definition. No external monotonicity certificate is used. -/
theorem gamma2_le_mul {T : Type*} (d e : T → T → ℝ≥0∞)
    (c : ℝ≥0∞) (hc : c ≠ ∞) (h : ∀ x y, d x y ≤ c * e x y) :
    gamma2 d ≤ c * gamma2 e := by
  by_cases hc0 : c = 0
  · have hd : d = fun _ _ => 0 := by
      funext x y
      exact le_antisymm (by simpa [hc0] using h x y) bot_le
    simp [hd, gamma2_zero, hc0]
  · unfold gamma2
    rw [ENNReal.mul_iInf_of_ne hc0 hc]
    apply iInf_mono
    intro P
    rw [ENNReal.mul_iSup]
    apply iSup_mono
    intro t
    rw [← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro k
    calc
      _ ≤ ENNReal.ofReal ((2 : ℝ) ^ ((k : ℝ) / 2)) *
          (c * cellDiameter e P k t) :=
        mul_le_mul_left' (cellDiameter_le_mul d e c h P k t) _
      _ = _ := by ac_rfl

end Paper29.Chaining
