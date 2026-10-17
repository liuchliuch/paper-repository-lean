import P31.LpEstimates
import P31.Localization

/-!
# Literal finite-coordinate form of Lemma 6.2

The hard function below is the actual affine-max/norm-max formula (6.3).
Its derivatives are taken on mathlib's ℓₚ space and represented by the ordinary
coordinate pairing.  Hölder's inequality supplies the required ℓ_q bound,
without a dimension factor.
-/

noncomputable section
open scoped BigOperators

namespace P31

open Set

variable {ι : Type*} [Fintype ι]
variable {M : ℕ} [NeZero M]

/-- The literal coordinate formula (6.3), with `i.val + 1` representing the
source indices `1, …, M`. -/
def vectorHardFunction (p : ℝ) (z : Fin M → ι → ℝ) (δ r : ℝ) (x : ι → ℝ) : ℝ :=
  max ((Finset.univ.sup' Finset.univ_nonempty
    (fun i : Fin M => (∑ j, z i j * x j) - ((i.val : ℝ) + 1) * δ)) / 2)
    (lpNorm p x - hardConstant M δ r)

/-- The same coordinate function viewed on its genuine ℓₚ normed space. -/
def vectorHardLift (p : ℝ) (z : Fin M → ι → ℝ) (δ r : ℝ)
    (x : PiLp (ENNReal.ofReal p) (fun _ : ι => ℝ)) : ℝ :=
  vectorHardFunction p z δ r (fun j => x j)

/-- The generic normed-space hard function is exactly the source formula,
including its finite maximum and its ℓₚ norm branch. -/
theorem vectorHardFunction_eq_hardFunction {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 0 < p) (z : Fin M → ι → ℝ) (δ r : ℝ) (x : ι → ℝ) :
    vectorHardFunction p z δ r x =
      hardFunction (fun i => coordinateFunctionalLp p (z i)) δ r
        (WithLp.toLp (ENNReal.ofReal p) x) := by
  unfold vectorHardFunction hardFunction hardAffineMax
  rw [← lpNorm_eq_piLp_norm p hp x]
  simp only [coordinateFunctionalLp_apply, PiLp.toLp_apply]

theorem vectorHardLift_eq_hardFunction {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 0 < p) (z : Fin M → ι → ℝ) (δ r : ℝ) :
    vectorHardLift p z δ r =
      hardFunction (fun i => coordinateFunctionalLp p (z i)) δ r := by
  funext x
  have hh := vectorHardFunction_eq_hardFunction hp z δ r (fun j => x j)
  exact hh

/-- The source hard function is convex; this proof goes through its actual
finite affine maximum and norm branch. -/
theorem vectorHardLift_convex {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 0 < p) (z : Fin M → ι → ℝ) (δ r : ℝ) :
    ConvexOn ℝ univ (vectorHardLift p z δ r) := by
  rw [vectorHardLift_eq_hardFunction hp z δ r]
  exact hardFunction_convex _ _ _

/-- Lemma 6.2 with the explicit coordinate ℓₚ and ℓ_q norms.  `s` is the
smoothed hard function and its error is measured against the literal formula
(6.3).  The gradient functional is the ordinary coordinate pairing. -/
theorem vector_hard_family_localization {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 1 < p) (z : Fin M → ι → ℝ) (δ μ η r : ℝ)
    (hδ : 0 < δ) (hμ : 0 < μ) (hr : 0 ≤ r)
    (s : PiLp (ENNReal.ofReal p) (fun _ : ι => ℝ) → ℝ)
    (hs : ConvexOn ℝ univ s)
    (herror : ∀ x : ι → ℝ,
      |s (WithLp.toLp (ENNReal.ofReal p) x) - vectorHardFunction p z δ r x| ≤ η)
    (x grad : ι → ℝ)
    (hd : HasFDerivAt (fun y => s y / μ) (coordinateFunctionalLp p grad)
      (WithLp.toLp (ENNReal.ofReal p) x)) :
    (1 - μ * lpNorm (dualExponent p) grad) * lpNorm p x ≤
      hardConstant M δ r - δ / 2 + 2 * η := by
  have he : ∀ y : PiLp (ENNReal.ofReal p) (fun _ : ι => ℝ),
      |s y - hardFunction (fun i => coordinateFunctionalLp p (z i)) δ r y| ≤ η := by
    intro y
    have hh := herror (fun j => y j)
    rw [vectorHardFunction_eq_hardFunction (by linarith) z δ r] at hh
    exact hh
  have hl := hard_family_localization (fun i => coordinateFunctionalLp p (z i))
    δ μ η r hδ hμ hr s hs he (WithLp.toLp (ENNReal.ofReal p) x)
    (coordinateFunctionalLp p grad) hd
  rw [← lpNorm_eq_piLp_norm p (by linarith) x] at hl
  have hg := coordinateFunctionalLp_norm_le hp grad
  have hn := lpNorm_nonneg p x
  have hmul := mul_le_mul_of_nonneg_left hg hμ.le
  have hmul' := mul_le_mul_of_nonneg_right hmul hn
  nlinarith

/-- The convexity-preserving smoothing form of the source lemma, with the
exact finite-coordinate hard function as the smoother input. -/
theorem vector_lemma6_2 {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 1 < p) (z : Fin M → ι → ℝ) (δ μ η r : ℝ)
    (hδ : 0 < δ) (hμ : 0 < μ) (hr : 0 ≤ r)
    (S : ((PiLp (ENNReal.ofReal p) (fun _ : ι => ℝ)) → ℝ) →
      (PiLp (ENNReal.ofReal p) (fun _ : ι => ℝ)) → ℝ)
    (hpres : ∀ f, ConvexOn ℝ univ f → ConvexOn ℝ univ (S f))
    (herror : ∀ x : ι → ℝ,
      |S (vectorHardLift p z δ r) (WithLp.toLp (ENNReal.ofReal p) x) -
        vectorHardFunction p z δ r x| ≤ η)
    (x grad : ι → ℝ)
    (hd : HasFDerivAt (fun y => S (vectorHardLift p z δ r) y / μ)
      (coordinateFunctionalLp p grad) (WithLp.toLp (ENNReal.ofReal p) x)) :
    (1 - μ * lpNorm (dualExponent p) grad) * lpNorm p x ≤
      hardConstant M δ r - δ / 2 + 2 * η :=
  vector_hard_family_localization hp z δ μ η r hδ hμ hr (S (vectorHardLift p z δ r))
    (hpres _ (vectorHardLift_convex (by linarith) z δ r)) herror x grad hd

/-- The output-radius bootstrap in the actual coordinate norms. -/
theorem vector_normalized_output_radius {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 1 < p) (z : Fin M → ι → ℝ) (δ μ η r ζ : ℝ)
    (hδ : 0 < δ) (hμ : 0 < μ) (hr0 : 0 ≤ r)
    (hr : r ≤ δ / 8) (hMδ : M * δ ≤ μ * ζ)
    (hη : η ≤ μ * ζ / 4) (hsmall : 4 * μ * ζ ≤ 1)
    (s : PiLp (ENNReal.ofReal p) (fun _ : ι => ℝ) → ℝ)
    (hs : ConvexOn ℝ univ s)
    (herror : ∀ x : ι → ℝ,
      |s (WithLp.toLp (ENNReal.ofReal p) x) - vectorHardFunction p z δ r x| ≤ η)
    (x grad : ι → ℝ)
    (hd : HasFDerivAt (fun y => s y / μ) (coordinateFunctionalLp p grad)
      (WithLp.toLp (ENNReal.ofReal p) x))
    (hg : μ * lpNorm (dualExponent p) grad ≤ 1 / 2) : lpNorm p x < 4 := by
  have hl := vector_hard_family_localization hp z δ μ η r hδ hμ hr0 s hs herror x grad hd
  have hc := normalized_constant_bound (M := M) δ μ η r ζ hδ hr hMδ hη hsmall
  have hn := lpNorm_nonneg p x
  nlinarith

/-- Equation (6.1) in the paper's ordinary coordinate pairing and exact
ℓₚ/ℓ_q norms.  Its supporting inequality comes from convexity and the actual
derivative, while Hölder supplies the final norm estimate. -/
theorem vector_convex_objective_gap {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 1 < p)
    (f : PiLp (ENNReal.ofReal p) (fun _ : ι => ℝ) → ℝ)
    (hc : ConvexOn ℝ univ f) (x y grad : ι → ℝ)
    (hd : HasFDerivAt f (coordinateFunctionalLp p grad)
      (WithLp.toLp (ENNReal.ofReal p) x)) :
    f (WithLp.toLp (ENNReal.ofReal p) x) -
      f (WithLp.toLp (ENNReal.ofReal p) y) ≤
      lpNorm (dualExponent p) grad * lpNorm p (x - y) := by
  have hh := convex_objective_gap hc hd (WithLp.toLp (ENNReal.ofReal p) y)
  have he : WithLp.toLp (ENNReal.ofReal p) x - WithLp.toLp (ENNReal.ofReal p) y =
      WithLp.toLp (ENNReal.ofReal p) (x - y) := rfl
  rw [he, ← lpNorm_eq_piLp_norm p (by linarith) (x - y)] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (coordinateFunctionalLp_norm_le hp grad)
    (lpNorm_nonneg p (x - y)))

/-- The localized normalized output solves the hard objective to tolerance
`ζ`, in literal coordinate notation. -/
theorem vector_normalized_objective_reduction {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 1 < p)
    (f : PiLp (ENNReal.ofReal p) (fun _ : ι => ℝ) → ℝ)
    (hc : ConvexOn ℝ univ f) (x y grad : ι → ℝ)
    (hd : HasFDerivAt f (coordinateFunctionalLp p grad)
      (WithLp.toLp (ENNReal.ofReal p) x))
    (ζ : ℝ) (hζ : 0 ≤ ζ) (hx : lpNorm p x ≤ 4) (hy : lpNorm p y ≤ 4)
    (hg : lpNorm (dualExponent p) grad ≤ ζ / 8) :
    f (WithLp.toLp (ENNReal.ofReal p) x) -
      f (WithLp.toLp (ENNReal.ofReal p) y) ≤ ζ := by
  have ht := lpNorm_add_le hp.le x (-y)
  rw [lpNorm_neg] at ht
  have hdist : lpNorm p (x - y) ≤ 8 := by
    rw [sub_eq_add_neg]
    linarith
  calc
    _ ≤ lpNorm (dualExponent p) grad * lpNorm p (x - y) :=
      vector_convex_objective_gap hp f hc x y grad hd
    _ ≤ (ζ / 8) * 8 := mul_le_mul hg hdist (lpNorm_nonneg p _) (by positivity)
    _ = ζ := by ring

end P31
