import Paper14.SieveDensityProbability
import Paper14.SieveResidualProbability
import Paper14.SieveRectangleGeometry

open MeasureTheory Set Function Filter
open scoped ENNReal
namespace Paper14
noncomputable section

/-- The original three-term void-probability estimate (20), with its
actual count, measure, finite sieve and prime-tail residual. -/
theorem primitive_void_bound {n : ℕ} {α K : ℝ} (P : ℕ) (hK : 1 < K)
    (hKM : K ≤ primorial P) (hα0 : 0 ≤ α/(n : ℝ)) (hα1 : α/(n : ℝ) < 1)
    (hβ : 0 < betaN (primorial P) ⌊2*(n : ℝ)/K⌋₊ (α/(n : ℝ))) :
    m {x | ZCount n α x = 0} ≤ ENNReal.ofReal
      ((K⁻¹)^2+8*(primorial P : ℝ)/betaN (primorial P) ⌊2*(n : ℝ)/K⌋₊ (α/(n : ℝ))+
       2*(α/(n : ℝ))*(⌊2*(n : ℝ)/K⌋₊ : ℝ)*SP P/betaN (primorial P) ⌊2*(n : ℝ)/K⌋₊ (α/(n : ℝ))) := by
  let Q : ℕ := ⌊2*(n : ℝ)/K⌋₊
  let ε : ℝ := α/(n : ℝ)
  let β : ℝ := betaN (primorial P) Q ε
  let A : Set (ℝ × ℝ) := {x ∈ Omega | K < cOf x}
  let C : Set (ℝ × ℝ) := {x | cOf x ≤ K ∧ (GM (primorial P) Q (cOf x) (thetaOf x) ε : ℝ) < β/2}
  let R : Set (ℝ × ℝ) := {x | β/2 ≤ (GM (primorial P) Q (cOf x) (thetaOf x) ε : ℝ)-
    (GPrim Q (cOf x) (thetaOf x) ε : ℝ)}
  letI : Fact (0 < (primorial P : ℝ)) := ⟨by exact_mod_cast primorial_pos P⟩
  have hsub : ∀ᵐ x ∂m, x ∈ {x | ZCount n α x = 0} → x ∈ A ∪ C ∪ R := by
    filter_upwards [ae_mem_Omega] with x hx
    intro hZ
    by_cases hc : cOf x ≤ K
    · have hprim := ZCount_zero_GPrim_zero hx hα0 hα1 (zero_lt_one.trans hK) hc hZ
      by_cases hg : (GM (primorial P) Q (cOf x) (thetaOf x) ε : ℝ) < β/2
      · exact Or.inl (Or.inr ⟨hc,hg⟩)
      · apply Or.inr
        change β/2 ≤ (GM (primorial P) Q (cOf x) (thetaOf x) ε : ℝ)-
          (GPrim Q (cOf x) (thetaOf x) ε : ℝ)
        rw [show GPrim Q (cOf x) (thetaOf x) ε = 0 from hprim,Nat.cast_zero,sub_zero]
        exact le_of_not_gt hg
    · exact Or.inl (Or.inl ⟨hx,lt_of_not_ge hc⟩)
  have hA : m A = ENNReal.ofReal ((K⁻¹)^2) := by
    change m {x ∈ Omega | K < x.1⁻¹} = _
    rw [m_tailC hK,← inv_sq_eq_rpow_neg_two (zero_lt_one.trans hK)]
  have hC : m C ≤ ENNReal.ofReal (8*(primorial P : ℝ)/β) :=
    sieve_small_count_measure (squarefree_primorial P) Q hKM hα0 hα1.le rfl hβ
  have hR : m R ≤ ENNReal.ofReal (2*ε*(Q : ℝ)*SP P/β) :=
    sieve_residual_markov P Q hα0 hα1.le hβ
  calc
    _ ≤ m (A ∪ C ∪ R) := measure_mono_ae hsub
    _ ≤ m A+m C+m R := (measure_union_le _ _).trans (add_le_add_right (measure_union_le _ _) _)
    _ ≤ ENNReal.ofReal ((K⁻¹)^2)+ENNReal.ofReal (8*(primorial P : ℝ)/β)+
        ENNReal.ofReal (2*ε*(Q : ℝ)*SP P/β) := by rw [hA]; exact add_le_add (add_le_add_left hC _) hR
    _ = _ := by
      rw [← ENNReal.ofReal_add (sq_nonneg _) (by positivity),← ENNReal.ofReal_add (by positivity)
        (div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hα0) (Nat.cast_nonneg _)) (SP_nonneg P)) hβ.le)]

end
end Paper14
