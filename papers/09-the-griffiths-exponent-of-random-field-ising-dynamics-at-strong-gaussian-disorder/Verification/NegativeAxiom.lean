import Paper09
open Real Filter MeasureTheory Paper09 Paper09.RFIM
open scoped Topology
noncomputable section
attribute [local instance] Classical.propDecidable
namespace Verification.Challenge
axiom forbidden_axiom (P : Prop) : P
theorem proposition_2_1_iid_actual (d : ℕ) (β : ℝ) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hd : 2 ≤ d) (hβ : 0 < β)
    (hsmall : (∃ (c : ℝ), 0 < c ∧ ∃ (α : ℝ), 0 < α ∧ ∃ (u₀ : ℝ), 0 < u₀ ∧
      ∀ u : ℝ, 0 < u → u ≤ u₀ → c*u^α ≤ ν.real {x : ℝ | |x| ≤ u}))
    (hsource : ∃ (c₀ : ℝ) (seq : ℕ → ℕ) (H : ℝ),
      0 < c₀ ∧ StrictMono seq ∧
      Tendsto (fun k => (seq (k+1):ℝ)/(seq k:ℝ)) atTop (𝓝 1) ∧
      (∀ᶠ k in atTop, ∃ ζ : Paper09.RFIM.Point d → Spin,
        pureBoxGap d (seq k) β ζ ≤ exp (-c₀*(seq k:ℝ)^(d-1))) ∧
      0 < H ∧
      2*(d:ℝ)*qH H d β*(exp (8*(d:ℝ)*β)-1+8*(d:ℝ)*β) ≤ c₀/4 ∧
      0 < ν.real (Set.Ici H) ∧ 0 < ν.real (Set.Iic (-H))) :
    ∃ c > 0, Tendsto (fun n : ℕ => (iidEnvironmentLaw d ν)
      {h | ¬ exp (c*(log (n:ℝ)/log (log (n:ℝ)))^exponentA d) ≤
        min (relaxationTime d n β h) (mixingTime d n β h)}) atTop (𝓝 0) :=
  forbidden_axiom _
end Verification.Challenge
