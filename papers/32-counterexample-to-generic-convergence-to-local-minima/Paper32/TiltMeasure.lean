import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic

namespace Paper32
open Set MeasureTheory

/-- The explicit bad-tilt square in (2.6). -/
def tiltSquare : Set (ℝ × ℝ) :=
  Ioo (-(1 / 100 : ℝ)) (1 / 100) ×ˢ Ioo (-(1 / 100 : ℝ)) (1 / 100)

/-- The positive-area initialization basin in (2.7). -/
def initialRectangle : Set (ℝ × ℝ) :=
  Ioo (-(1 / 80 : ℝ)) (1 / 80) ×ˢ Ioo (-(1 / 20 : ℝ)) (1 / 20)

theorem mem_tiltSquare (v : ℝ × ℝ) :
    v ∈ tiltSquare ↔ |v.1| < 1 / 100 ∧ |v.2| < 1 / 100 := by
  simp only [tiltSquare, mem_prod, mem_Ioo, abs_lt]

theorem mem_initialRectangle (z : ℝ × ℝ) :
    z ∈ initialRectangle ↔ |z.1| < 1 / 80 ∧ |z.2| < 1 / 20 := by
  simp only [initialRectangle, mem_prod, mem_Ioo, abs_lt]

theorem volume_tiltSquare : volume tiltSquare = ENNReal.ofReal (1 / 2500 : ℝ) := by
  rw [tiltSquare, Measure.volume_eq_prod, Measure.prod_prod]
  simp only [Real.volume_Ioo]
  rw [← ENNReal.ofReal_mul (by norm_num)]
  norm_num

theorem volume_initialRectangle : volume initialRectangle = ENNReal.ofReal (1 / 400 : ℝ) := by
  rw [initialRectangle, Measure.volume_eq_prod, Measure.prod_prod]
  simp only [Real.volume_Ioo]
  rw [← ENNReal.ofReal_mul (by norm_num)]
  norm_num

/-- The measure-theoretic contradiction used at the end of Corollary 2.5.
The algorithmic counterexample for each tilt is a separate mathematical input. -/
theorem conull_intersects_tiltSquare {G : Set (ℝ × ℝ)} (hG : volume Gᶜ = 0) :
    (G ∩ tiltSquare).Nonempty := by
  by_contra h
  have hsub : tiltSquare ⊆ Gᶜ := by
    intro v hv hvG
    exact h ⟨v, hvG, hv⟩
  have hz : volume tiltSquare = 0 := le_antisymm ((measure_mono hsub).trans_eq hG) (zero_le _)
  rw [volume_tiltSquare] at hz
  norm_num at hz

theorem no_conull_set_of_bad_square {Good : (ℝ × ℝ) → Prop}
    (hbad : ∀ v ∈ tiltSquare, ¬ Good v) :
    ¬ ∃ G : Set (ℝ × ℝ), volume Gᶜ = 0 ∧ ∀ v ∈ G, Good v := by
  rintro ⟨G, hG, hgood⟩
  rcases conull_intersects_tiltSquare hG with ⟨v, hvG, hvU⟩
  exact hbad v hvU (hgood v hvG)

end Paper32
