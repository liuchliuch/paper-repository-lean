import P31.UpperBound
import P31.Checkpoints
import P31.LowerBound

/-! Source-level connections: the proved base method supplies both the
accuracy-oblivious wrapper and the upper half of the conditional minimax result.
Only the explicitly named literature inputs are parameters. -/
noncomputable section
open scoped BigOperators
namespace P31
open QueryProgram Schedule
variable {ι : Type*} [Fintype ι]

def checkpointConstant (C p κ : ℝ) : ℝ :=
  2 * queryConstant C (vectorBiasCoefficient p) p κ * (2:ℝ)^beta p κ /
    ((2:ℝ)^beta p κ-1)

lemma checkpointConstant_pos {C p κ : ℝ} (hC : 0 ≤ C) (hp : 2 ≤ p) (hκ : 1 < κ) :
    0 < checkpointConstant C p κ := by
  have hb := beta_pos hp hκ
  have ht : 1 < (2:ℝ)^beta p κ := Real.one_lt_rpow (by norm_num) hb
  exact div_pos (mul_pos (mul_pos (by norm_num)
    (queryConstant_pos hC (vectorBiasCoefficient_pos p) hp hκ)) (by positivity)) (by linarith)

/-- The actual target-accuracy-free procedure uses only L,R,p,kappa and the
known initial point.  Its constructor has no requested epsilon or objective. -/
def vectorCheckpointMethod {C : ℝ} (p κ L R : ℝ) (initial : ι → ℝ)
    (hp : 2 ≤ p) (hκ : 1 < κ) (hκhi : κ ≤ 2)
    (engine : ExternalComplementaryComposite ι p κ C) (j : ℕ) :
    Program (ι → ℝ) (ι → ℝ) (ι → ℝ) :=
  if L*R^(κ-1)=0 then .pure initial else
    checkpointProgram (fun ε => vectorGradientMethod p κ L R ε initial hp hκ hκhi engine)
      initial (L*R^(κ-1)) j

/-- Corollary5.2, connected to the actual base method, including the M=0
zero-query regime.  The constant is independent of d,L,R and j. -/
theorem corollary5_2 {p κ C L R : ℝ}
    (hp : 2 ≤ p) (hκ : 1 < κ) (hκhi : κ ≤ 2) (hC : 0 ≤ C)
    (hL : 0 ≤ L) (hR : 0 ≤ R) (hClarkson : ScalarWeightedClarkson p)
    (engine : ExternalComplementaryComposite ι p κ C)
    (initial : ι → ℝ) (f : (ι → ℝ) → ℝ) (grad : (ι → ℝ) → ι → ℝ)
    (hf : ConvexOn ℝ Set.univ f)
    (hg : ∀ x, HasFDerivAt f (coordinateFunctional (grad x)) x)
    (hh : ∀ x y, lpNorm (dualExponent p) (grad x-grad y) ≤ L * lpNorm p (x-y)^(κ-1))
    (xstar : ι → ℝ) (hstar : ∀ y, f xstar ≤ f y) (hr : lpNorm p (initial-xstar) ≤ R) :
    0 < checkpointConstant C p κ ∧ ∀ j : ℕ, 1 ≤ j →
      lpNorm (dualExponent p) (grad ((vectorCheckpointMethod p κ L R initial hp hκ hκhi engine j).run grad).value)
        ≤ L*R^(κ-1)/(2:ℝ)^j ∧
      (((vectorCheckpointMethod p κ L R initial hp hκ hκhi engine j).run grad).calls : ℝ) ≤
        checkpointConstant C p κ * (2:ℝ)^((j:ℝ)*beta p κ) := by
  have hK := queryConstant_pos hC (vectorBiasCoefficient_pos p) hp hκ
  have hCC := checkpointConstant_pos hC hp hκ
  refine ⟨hCC, ?_⟩
  by_cases hzero : L*R^(κ-1)=0
  · have hnorm : lpNorm (dualExponent p) (grad initial) ≤ 0 :=
      vector_zero_query_bound (by linarith) grad initial xstar hL (by linarith) hh
        (vector_gradient_zero_at_minimizer f grad xstar (hg _) hstar) hr (by rw [hzero])
    intro j hj
    have hc : (0:ℝ) ≤ checkpointConstant C p κ * (2:ℝ)^((j:ℝ)*beta p κ) :=
      mul_nonneg hCC.le (Real.rpow_nonneg (by norm_num) _)
    simpa [vectorCheckpointMethod, hzero] using And.intro hnorm hc
  · have hM : 0 < L*R^(κ-1) := lt_of_le_of_ne
      (mul_nonneg hL (Real.rpow_nonneg hR _)) (Ne.symm hzero)
    have hbase := accuracy_oblivious_checkpoints hM hK.le (beta_pos hp hκ)
      (fun ε => vectorGradientMethod p κ L R ε initial hp hκ hκhi engine)
      initial grad (fun x => lpNorm (dualExponent p) (grad x))
      (fun ε hε => vectorGradientMethod_guarantee hp hκ hκhi hC hL hR hε hClarkson
        engine initial f grad hf hg hh xstar hstar hr)
    intro j hj
    simpa only [vectorCheckpointMethod, if_neg hzero, checkpointConstant] using hbase j hj

namespace LowerBound

/-- Convert the gradient-only coordinate method to a value-gradient PiLp
method by exact point/reply simulation. This discharges the upper hypothesis
in the conditional comparison rather than assuming that comparison. -/
def vectorUpperMethod {p κ C : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 2 ≤ p) (hκ : 1 < κ) (hκhi : κ ≤ 2)
    (source : ExternalCompositeFamily p κ C) (d : ℕ) (hd : 0 < d) (L R ε : ℝ) : Method p d :=
  (Program.simulate (WithLp.toLp (ENNReal.ofReal p)) (fun (_ : Fin d → ℝ) (reply : Reply d) => reply.2)
    (vectorGradientMethod p κ L R ε (0 : Fin d → ℝ) hp hκ hκhi (source d hd))).map
      (WithLp.toLp (ENNReal.ofReal p))

lemma coordinateFunctionalLp_comp_toLp {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (d : ℕ) (v : Fin d → ℝ) :
    (coordinateFunctionalLp p v).comp
      (PiLp.continuousLinearEquiv (ENNReal.ofReal p) ℝ (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap =
      coordinateFunctional v := by
  ext x
  simp [coordinateFunctionalLp]

/-- Theorem1.2 supplies a feasible uniform budget in the exact oracle model
used by Assumption6.1. Its constant precedes all dimensions and scale parameters. -/
theorem upper_feasible_from_composite {p κ C : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 2 ≤ p) (hκ : 1 < κ) (hκhi : κ ≤ 2) (hC : 0 ≤ C)
    (hClarkson : ScalarWeightedClarkson p) (source : ExternalCompositeFamily p κ C)
    (d : ℕ) (hd : 1 ≤ d) (L R ε : ℝ) (hL : 0 < L) (hR : 0 < R) (hε : 0 < ε) :
    FeasibleBudget (p := p) (κ := κ) (d := d) L R ε
      (Schedule.queryConstant C (vectorBiasCoefficient p) p κ *
        (1+(L*R^(κ-1)/ε)^exponent p κ)) := by
  have hd0 : 0 < d := hd
  let e := PiLp.continuousLinearEquiv (ENNReal.ofReal p) ℝ (fun _ : Fin d => ℝ)
  let P := vectorUpperMethod hp hκ hκhi source d hd0 L R ε
  have hK := Schedule.queryConstant_pos hC (vectorBiasCoefficient_pos p) hp hκ
  have hvalid (I : VectorInstance p κ d) (hI : I.InClass L R) :
      lpNorm (dualExponent p) (I.gradient (P.run I.oracle).value) ≤ ε ∧
      ((P.run I.oracle).calls : ℝ) ≤ Schedule.queryConstant C (vectorBiasCoefficient p) p κ *
        (1+(L*R^(κ-1)/ε)^exponent p κ) := by
    let f : (Fin d → ℝ) → ℝ := fun x => I.value (WithLp.toLp (ENNReal.ofReal p) x)
    let grad : (Fin d → ℝ) → Fin d → ℝ := fun x => I.gradient (WithLp.toLp (ENNReal.ofReal p) x)
    have hf : ConvexOn ℝ Set.univ f := by
      simpa [f, e] using I.convex.comp_linearMap e.symm.toLinearMap
    have hg : ∀ x, HasFDerivAt f (coordinateFunctional (grad x)) x := by
      intro x
      have h := (I.derivative (e.symm x)).comp x e.symm.hasFDerivAt
      rw [coordinateFunctionalLp_comp_toLp] at h
      exact h
    have hh : ∀ x y, lpNorm (dualExponent p) (grad x-grad y) ≤ L*lpNorm p (x-y)^(κ-1) := by
      intro x y
      have h := hI.1 (e.symm x) (e.symm y)
      change lpNorm (dualExponent p) (grad x-grad y) ≤
        L * ‖(WithLp.toLp (ENNReal.ofReal p) (x-y) : Point p d)‖^(κ-1) at h
      rw [← lpNorm_eq_piLp_norm p (by linarith : 0 < p)] at h
      exact h
    obtain ⟨ystar, hstar, hradius⟩ := hI.2
    let xstar : Fin d → ℝ := e ystar
    have hm : ∀ y, f xstar ≤ f y := fun y => by simpa [f, xstar] using hstar (e.symm y)
    have hr : lpNorm p ((0 : Fin d → ℝ)-xstar) ≤ R := by
      rw [zero_sub, lpNorm_neg, lpNorm_eq_piLp_norm p (by linarith : 0 < p)]
      change ‖ystar‖ ≤ R
      exact hradius
    have hv := vectorGradientMethod_guarantee hp hκ hκhi hC hL.le hR.le hε hClarkson
      (source d hd0) 0 f grad hf hg hh xstar hm hr
    simpa only [P, vectorUpperMethod, Program.run_map, Program.run_simulate,
      VectorInstance.oracle, grad, exponent, Schedule.beta, Schedule.deltaDenom] using hv
  refine ⟨mul_nonneg hK.le (by positivity), P, ?_, ?_⟩
  · intro I hI
    exact (hvalid I hI).1
  · intro I hI
    exact (hvalid I hI).2

/-- Corollary1.3 with its upper half discharged by the actual accumulated
method. Explicit inputs are the two known upper ingredients and the source's
own simultaneous hard-family assumption. -/
theorem corollary1_3_from_composite {p κ C : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 2 ≤ p) (hκ : 1 < κ) (hκhi : κ ≤ 2) (hC : 0 ≤ C)
    (hClarkson : ScalarWeightedClarkson p) (source : ExternalCompositeFamily p κ C)
    (H : SimultaneousHardFamily p κ) :
    ∃ cAccuracy CLowerDimension cLower CUpper : ℝ,
      0 < cAccuracy ∧ 0 < CLowerDimension ∧ 0 < cLower ∧ 0 < CUpper ∧
      ∀ (d : ℕ), 1 ≤ d → ∀ (L R ε : ℝ), 0 < L → 0 < R → 0 < ε →
        ε ≤ cAccuracy*(L*R^(κ-1)) → p ≤ Real.log (d:ℝ) →
        CLowerDimension*(L*R^(κ-1)/ε)^exponent p κ ≤ d →
        cLower*(L*R^(κ-1)/ε)^exponent p κ ≤ complexity (p:=p) (κ:=κ) (d:=d) L R ε ∧
        complexity (p:=p) (κ:=κ) (d:=d) L R ε ≤ CUpper*(L*R^(κ-1)/ε)^exponent p κ := by
  exact corollary1_3 H hp hκ hκhi (Schedule.queryConstant C (vectorBiasCoefficient p) p κ)
    (Schedule.queryConstant_pos hC (vectorBiasCoefficient_pos p) hp hκ)
    (upper_feasible_from_composite hp hκ hκhi hC hClarkson source)

end LowerBound
end P31
