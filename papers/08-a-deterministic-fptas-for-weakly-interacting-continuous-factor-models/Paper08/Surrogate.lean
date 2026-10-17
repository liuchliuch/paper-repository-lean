import Paper08.Integral
import Paper08.SmallDegree
import Paper08.FPTAS

/-!
Uniform approximation of local factors transfers to the actual partition
integral, including overlapping scopes.  This is the integration step in the
upper-bound paragraph of Proposition B.1; no claim about grid construction or
oracle running time is made by this analytic transfer theorem.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Paper08.Surrogate
open Integral

theorem partitionFunction_ge_one {n : ℕ} {ι : Type*} [Fintype ι]
    (f : ι → (Fin n → ℝ) → ℝ)
    (hf : IntegrableOn (fun x => ∏ i, f i x) (cube n))
    (hlo : ∀ x ∈ cube n, ∀ i, 1 ≤ f i x) :
    1 ≤ partitionFunction n f := by
  apply le_cubeIntegral hf
  intro x hx
  apply Finset.prod_induction (f := fun i => f i x) (p := fun z : ℝ => 1 ≤ z)
  · intro a b ha hb
    nlinarith
  · norm_num
  · intro i _
    exact hlo x hx i

/-- A pointwise multiplicative bound survives integration over the cube. -/
theorem integral_ratio_bounds {n : ℕ} {f g : (Fin n → ℝ) → ℝ} {ε : ℝ}
    (hf : IntegrableOn f (cube n)) (hg : IntegrableOn g (cube n))
    (hpos : 0 < cubeIntegral f)
    (hpoint : ∀ x ∈ cube n,
      Real.exp (-ε) * f x ≤ g x ∧ g x ≤ Real.exp ε * f x) :
    Real.exp (-ε) ≤ cubeIntegral g / cubeIntegral f ∧
      cubeIntegral g / cubeIntegral f ≤ Real.exp ε := by
  have hlow := setIntegral_mono_on (hf.const_mul (Real.exp (-ε))) hg
    (measurableSet_cube n) (fun x hx => (hpoint x hx).1)
  have hupp := setIntegral_mono_on hg (hf.const_mul (Real.exp ε))
    (measurableSet_cube n) (fun x hx => (hpoint x hx).2)
  simp only [integral_const_mul] at hlow hupp
  exact ⟨(le_div_iff₀ hpos).mpr hlow, (div_le_iff₀ hpos).mpr hupp⟩

/-- The logarithmic error in the partition integrals is at most the total
uniform absolute error budget in factors that are each at least one. -/
theorem partitionFunction_accurate {n : ℕ} {ι : Type*} [Fintype ι]
    (f g : ι → (Fin n → ℝ) → ℝ) {δ : ℝ}
    (hf : IntegrableOn (fun x => ∏ i, f i x) (cube n))
    (hg : IntegrableOn (fun x => ∏ i, g i x) (cube n))
    (hlo : ∀ x ∈ cube n, ∀ i, 1 ≤ f i x)
    (hgo : ∀ x ∈ cube n, ∀ i, 1 ≤ g i x)
    (herr : ∀ x ∈ cube n, ∀ i, |g i x - f i x| ≤ δ) :
    FPTAS.Accurate (partitionFunction n g) (partitionFunction n f)
      (Fintype.card ι * δ) := by
  classical
  have hZ := partitionFunction_ge_one f hf hlo
  have hG := partitionFunction_ge_one g hg hgo
  have hZpos : 0 < partitionFunction n f := lt_of_lt_of_le zero_lt_one hZ
  have hGpos : 0 < partitionFunction n g := lt_of_lt_of_le zero_lt_one hG
  have hratio := integral_ratio_bounds hf hg hZpos (fun x hx => by
    have hlog := (SmallDegree.component_log_error Finset.univ
      (fun i => f i x) (fun i => g i x) (fun i _ => hlo x hx i)
      (fun i _ => hgo x hx i)).trans
        (Finset.sum_le_sum (fun i _ => herr x hx i))
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hlog
    have hpf : 0 < ∏ i, f i x := Finset.prod_pos (fun i _ =>
      lt_of_lt_of_le zero_lt_one (hlo x hx i))
    have hpg : 0 < ∏ i, g i x := Finset.prod_pos (fun i _ =>
      lt_of_lt_of_le zero_lt_one (hgo x hx i))
    have he := FPTAS.accurate_exp_form ⟨hpf, hpg, hlog⟩
    exact ⟨(le_div_iff₀ hpf).mp he.1, (div_le_iff₀ hpf).mp he.2⟩)
  refine ⟨hZpos, hGpos, ?_⟩
  have hdiv : 0 < partitionFunction n g / partitionFunction n f := div_pos hGpos hZpos
  have hloglo := Real.log_le_log (Real.exp_pos _) hratio.1
  have hloghi := Real.log_le_log hdiv hratio.2
  rw [Real.log_exp] at hloglo hloghi
  change -(Fintype.card ι * δ) ≤
    Real.log (partitionFunction n g / partitionFunction n f) at hloglo
  rw [Real.log_div hGpos.ne' hZpos.ne'] at hloglo hloghi
  exact abs_le.mpr ⟨hloglo, hloghi⟩

end Paper08.Surrogate
