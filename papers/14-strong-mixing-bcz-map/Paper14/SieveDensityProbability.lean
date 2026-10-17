import Paper14.CoordinateDomination
import Paper14.SieveActualMoments

open MeasureTheory Set Function Filter
open scoped ENNReal
namespace Paper14
noncomputable section

/-- Actual density comparison and Chebyshev estimate (18). -/
theorem sieve_small_count_measure {M : ℕ} [hMp : Fact (0 < (M : ℝ))]
    (hM : Squarefree M) (Q : ℕ) {K ε β : ℝ} (hKM : K ≤ M)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hβeq : β = betaN M Q ε) (hβ : 0 < β) :
    m {x | cOf x ≤ K ∧ (GM M Q (cOf x) (thetaOf x) ε : ℝ) < β/2} ≤
      ENNReal.ofReal (8*(M : ℝ)/β) := by
  let A : Set (ℝ × ℝ) := {z | (GM M Q z.1 z.2 ε : ℝ) < β/2}
  have hn : Measurable (fun z : ℝ × ℝ => GM M Q z.1 z.2 ε) := measurable_GM M Q hε1
  have hg : Measurable (fun z : ℝ × ℝ => (GM M Q z.1 z.2 ε : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hn
  have hA : MeasurableSet A := measurableSet_lt hg measurable_const
  have hc : Measurable cOf := by unfold cOf; fun_prop
  have hco : Measurable (fun x : ℝ × ℝ => (cOf x,thetaOf x)) := by unfold cOf thetaOf; fun_prop
  let E : Set (ℝ × ℝ) := {x | cOf x ≤ K ∧ (cOf x,thetaOf x) ∈ A}
  have hE : MeasurableSet E := (measurableSet_le hc measurable_const).inter (hco hA)
  have hd := farey_coordinate_truncation_bound M hKM (A.indicator (fun _ => (1 : ℝ≥0∞)))
    (measurable_const.indicator hA)
  have hleft : (fun x => if cOf x ≤ K then A.indicator (fun _ => (1 : ℝ≥0∞)) (cOf x,thetaOf x) else 0) =
      E.indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext x
    by_cases hk : cOf x ≤ K <;> by_cases ha : (cOf x,thetaOf x) ∈ A <;> simp [E,hk,ha]
  have hright : (fun z : ℝ × ℝ => A.indicator (fun _ => (1 : ℝ≥0∞)) (z.2,z.1)) =
      (Prod.swap ⁻¹' A).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext z
    have hzp : z ∈ Prod.swap ⁻¹' A ↔ (z.2,z.1) ∈ A := Iff.rfl
    by_cases hz : (z.2,z.1) ∈ A
    · rw [indicator_of_mem hz,indicator_of_mem (hzp.mpr hz)]
    · rw [indicator_of_notMem hz,indicator_of_notMem (fun h => hz (hzp.mp h))]
  rw [hleft,hright,lintegral_indicator hE,lintegral_one,Measure.restrict_apply_univ,
    lintegral_indicator (hA.preimage measurable_swap),lintegral_one,Measure.restrict_apply_univ] at hd
  have hcheb : sieveAuxMeasure M (Prod.swap ⁻¹' A) ≤ ENNReal.ofReal (4/β) := by
    subst β
    exact GM_aux_lower_tail hM Q hε0 hε1 hβ
  have hmul : 2*ENNReal.ofReal (M : ℝ)*ENNReal.ofReal (4/β) = ENNReal.ofReal (8*(M : ℝ)/β) := by
    calc
      _ = ENNReal.ofReal (2*(M : ℝ))*ENNReal.ofReal (4/β) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),ENNReal.ofReal_ofNat]
      _ = ENNReal.ofReal ((2*(M : ℝ))*(4/β)) :=
        (ENNReal.ofReal_mul (mul_nonneg (by norm_num) (Nat.cast_nonneg _))).symm
      _ = _ := congrArg ENNReal.ofReal (by ring)
  exact hd.trans ((mul_le_mul_left' hcheb _).trans_eq hmul)

end
end Paper14
