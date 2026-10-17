import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Localization of the coercive hard family (Section 6)

The derivative is represented by a continuous linear functional, so its operator
norm is exactly the dual norm.  The proof applies in every real normed space,
in particular to finite dimensional ℓₚ and Schatten spaces.
-/

namespace P31

open Set

section Support

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The supporting-hyperplane inequality follows from genuine convexity and
Fréchet differentiability; it is not an assumption on the gradient. -/
theorem convex_support {f : E → ℝ} (hc : ConvexOn ℝ univ f)
    {x : E} {g : E →L[ℝ] ℝ} (hd : HasFDerivAt f g x) (y : E) :
    f x + g (y - x) ≤ f y := by
  let l : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x y
  have hl : HasDerivAt l (y - x) 0 := by
    change HasDerivAt (fun t : ℝ => t • (y - x) + x) (y - x) 0
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (y - x)).add_const x
  have hc' : ConvexOn ℝ univ (f ∘ l) := by
    simpa only [preimage_univ] using hc.comp_affineMap l
  have hd' : HasDerivAt (f ∘ l) (g (y - x)) 0 := by
    have hd0 : HasFDerivAt f g (l 0) := by
      simpa only [l, AffineMap.lineMap_apply_zero] using hd
    exact hd0.comp_hasDerivAt 0 hl
  have hs := hc'.le_slope_of_hasDerivAt (mem_univ 0) (mem_univ 1)
    (by norm_num : (0 : ℝ) < 1) hd'
  have h : g (y - x) ≤ f y - f x := by simpa [slope_def_field, l] using hs
  linarith

/-- Equation (6.1), with the gradient regarded as a dual functional. -/
theorem convex_objective_gap {f : E → ℝ} (hc : ConvexOn ℝ univ f)
    {x : E} {g : E →L[ℝ] ℝ} (hd : HasFDerivAt f g x) (y : E) :
    f x - f y ≤ ‖g‖ * ‖x - y‖ := by
  have hs := convex_support hc hd y
  have hn := g.le_opNorm (x - y)
  have ha : g (x - y) ≤ ‖g‖ * ‖x - y‖ := (le_abs_self _).trans hn
  have he : g (y - x) = -g (x - y) := by rw [← map_neg, neg_sub]
  rw [he] at hs
  linarith

end Support

section HardFamily

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : ℕ} [NeZero M]

/-- The value of `C` in equation (6.3). -/
noncomputable def hardConstant (M : ℕ) (δ r : ℝ) : ℝ :=
  (3 * (1 + r) + M * δ) / 2

/-- The inner finite maximum in (6.3); Fin indices are shifted by one. -/
noncomputable def hardAffineMax (z : Fin M → E →L[ℝ] ℝ) (δ : ℝ) (x : E) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun i : Fin M => z i x - ((i.val : ℝ) + 1) * δ)

/-- The actual hard function, including the coercive norm branch. -/
noncomputable def hardFunction (z : Fin M → E →L[ℝ] ℝ) (δ r : ℝ) (x : E) : ℝ :=
  max (hardAffineMax z δ x / 2) (‖x‖ - hardConstant M δ r)

lemma hardConstant_gt_half (δ r : ℝ) (hδ : 0 < δ) (hr : 0 ≤ r) :
    δ / 2 < hardConstant M δ r := by
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne M)
  have hmδ : δ ≤ M * δ := by nlinarith
  unfold hardConstant
  linarith

lemma hardAffineMax_zero (z : Fin M → E →L[ℝ] ℝ) (δ : ℝ) (hδ : 0 ≤ δ) :
    hardAffineMax z δ 0 = -δ := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro i hi
    simp only [map_zero, zero_sub]
    have hi0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
    nlinarith
  · have hzero : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
    let i : Fin M := ⟨0, hzero⟩
    have hh := Finset.le_sup' (f := fun j : Fin M => z j (0 : E) -
      ((j.val : ℝ) + 1) * δ) (Finset.mem_univ i)
    simpa [hardAffineMax, i] using hh

/-- A finite maximum of the source affine functions is convex. -/
lemma hardAffineMax_convex (z : Fin M → E →L[ℝ] ℝ) (δ : ℝ) :
    ConvexOn ℝ univ (hardAffineMax z δ) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  apply Finset.sup'_le
  intro i hi
  have hix : z i x - ((i.val : ℝ) + 1) * δ ≤ hardAffineMax z δ x :=
    Finset.le_sup' (f := fun j : Fin M => z j x - ((j.val : ℝ) + 1) * δ) (Finset.mem_univ i)
  have hiy : z i y - ((i.val : ℝ) + 1) * δ ≤ hardAffineMax z δ y :=
    Finset.le_sup' (f := fun j : Fin M => z j y - ((j.val : ℝ) + 1) * δ) (Finset.mem_univ i)
  have hax := mul_le_mul_of_nonneg_left hix ha
  have hby := mul_le_mul_of_nonneg_left hiy hb
  simp only [map_add, map_smul, smul_eq_mul]
  have he : a * (z i x - ((i.val : ℝ) + 1) * δ) +
      b * (z i y - ((i.val : ℝ) + 1) * δ) =
      a * z i x + b * z i y - ((i.val : ℝ) + 1) * δ := by
    calc
      _ = a * z i x + b * z i y - (a + b) * (((i.val : ℝ) + 1) * δ) := by ring
      _ = _ := by rw [hab]; ring
  change a * z i x + b * z i y - ((i.val : ℝ) + 1) * δ ≤
    a * hardAffineMax z δ x + b * hardAffineMax z δ y
  linarith

/-- The convexity-preserving smoothing hypothesis can be applied to the
actual hard function because both its finite affine maximum and norm branch
are convex. -/
lemma hardFunction_convex (z : Fin M → E →L[ℝ] ℝ) (δ r : ℝ) :
    ConvexOn ℝ univ (hardFunction z δ r) := by
  have ha : ConvexOn ℝ univ (fun x => hardAffineMax z δ x / 2) := by
    simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using
      ConvexOn.smul (by norm_num : (0 : ℝ) ≤ 2⁻¹) (hardAffineMax_convex z δ)
  have hn : ConvexOn ℝ univ (fun x : E => ‖x‖ - hardConstant M δ r) := by
    simpa only [Pi.add_apply, sub_eq_add_neg] using
      (convexOn_norm (E := E) convex_univ).add_const (-hardConstant M δ r)
  exact ha.sup hn

/-- At the origin the first affine branch is maximal and the norm branch is
strictly lower, giving exactly the origin value used in Lemma 6.2. -/
lemma hardFunction_zero (z : Fin M → E →L[ℝ] ℝ) (δ r : ℝ)
    (hδ : 0 < δ) (hr : 0 ≤ r) :
    hardFunction z δ r 0 = -δ / 2 := by
  unfold hardFunction
  rw [hardAffineMax_zero z δ hδ.le, norm_zero, zero_sub]
  apply max_eq_left
  have hh := hardConstant_gt_half (M := M) δ r hδ hr
  linarith

lemma hardFunction_norm_lower (z : Fin M → E →L[ℝ] ℝ) (δ r : ℝ) (x : E) :
    ‖x‖ - hardConstant M δ r ≤ hardFunction z δ r x :=
  le_max_right _ _

/-- Lemma 6.2.  `s` is the smoothed hard function.  Convexity is imposed on
`s`, as provided by a convexity-preserving smoother, and the uniform error is
imposed on the actual max function (6.3). -/
theorem hard_family_localization
    (z : Fin M → E →L[ℝ] ℝ) (δ μ η r : ℝ)
    (hδ : 0 < δ) (hμ : 0 < μ) (hr : 0 ≤ r)
    (s : E → ℝ) (hs : ConvexOn ℝ univ s)
    (herror : ∀ x, |s x - hardFunction z δ r x| ≤ η)
    (x : E) (g : E →L[ℝ] ℝ)
    (hd : HasFDerivAt (fun y => s y / μ) g x) :
    (1 - μ * ‖g‖) * ‖x‖ ≤ hardConstant M δ r - δ / 2 + 2 * η := by
  have hnorm := hardFunction_norm_lower z δ r x
  have hlower := (abs_le.mp (herror x)).1
  have hupper := (abs_le.mp (herror 0)).2
  rw [hardFunction_zero z δ r hδ hr] at hupper
  have hc : ConvexOn ℝ univ (fun y => s y / μ) := by
    simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using ConvexOn.smul (inv_nonneg.mpr hμ.le) hs
  have hsupp := convex_support hc hd (0 : E)
  have hbound : g x ≤ ‖g‖ * ‖x‖ :=
    (le_abs_self _).trans (g.le_opNorm x)
  simp only [zero_sub, map_neg] at hsupp
  have hsupp' : s x ≤ s 0 + μ * g x := by
    have := (div_le_div_iff_of_pos_right hμ).mp
      (show s x / μ ≤ (s 0 + μ * g x) / μ by
        calc
          s x / μ ≤ s 0 / μ + g x := by linarith
          _ = (s 0 + μ * g x) / μ := by field_simp)
    exact this
  have hmult := mul_le_mul_of_nonneg_left hbound hμ.le
  nlinarith

/-- Lemma 6.2 with a convexity-preserving smoothing operator.  Its locality
and the unit norm bounds on `z` are needed by the external hard-family
construction, but the localization proof is valid without those extra
restrictions. -/
theorem lemma6_2
    (z : Fin M → E →L[ℝ] ℝ) (δ μ η r : ℝ)
    (hδ : 0 < δ) (hμ : 0 < μ) (hr : 0 ≤ r)
    (S : (E → ℝ) → E → ℝ)
    (hpres : ∀ f, ConvexOn ℝ univ f → ConvexOn ℝ univ (S f))
    (herror : ∀ x, |S (hardFunction z δ r) x - hardFunction z δ r x| ≤ η)
    (x : E) (g : E →L[ℝ] ℝ)
    (hd : HasFDerivAt (fun y => S (hardFunction z δ r) y / μ) g x) :
    (1 - μ * ‖g‖) * ‖x‖ ≤ hardConstant M δ r - δ / 2 + 2 * η :=
  hard_family_localization z δ μ η r hδ hμ hr
    (S (hardFunction z δ r)) (hpres _ (hardFunction_convex z δ r)) herror x g hd

/-- The exact constant estimate in (6.6), from the simultaneous parameter
conditions (6.5). -/
theorem normalized_constant_bound (δ μ η r ζ : ℝ)
    (hδ : 0 < δ) (hr : r ≤ δ / 8)
    (hMδ : M * δ ≤ μ * ζ) (hη : η ≤ μ * ζ / 4)
    (hsmall : 4 * μ * ζ ≤ 1) :
    2 * (hardConstant M δ r - δ / 2 + 2 * η) < 4 := by
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne M)
  have hδζ : δ ≤ μ * ζ := (by nlinarith : δ ≤ M * δ).trans hMδ
  unfold hardConstant
  nlinarith

/-- Every sufficiently small-gradient output lies in the fixed radius-four
ball.  This is the localization bootstrap used in Corollary 1.3. -/
theorem normalized_output_radius
    (z : Fin M → E →L[ℝ] ℝ) (δ μ η r ζ : ℝ)
    (hδ : 0 < δ) (hμ : 0 < μ) (hr0 : 0 ≤ r)
    (hr : r ≤ δ / 8) (hMδ : M * δ ≤ μ * ζ)
    (hη : η ≤ μ * ζ / 4) (hsmall : 4 * μ * ζ ≤ 1)
    (s : E → ℝ) (hs : ConvexOn ℝ univ s)
    (herror : ∀ x, |s x - hardFunction z δ r x| ≤ η)
    (x : E) (g : E →L[ℝ] ℝ)
    (hd : HasFDerivAt (fun y => s y / μ) g x)
    (hg : μ * ‖g‖ ≤ 1 / 2) : ‖x‖ < 4 := by
  have hl := hard_family_localization z δ μ η r hδ hμ hr0 s hs herror x g hd
  have hc := normalized_constant_bound (M := M) δ μ η r ζ hδ hr hMδ hη hsmall
  have hn := norm_nonneg x
  nlinarith

/-- The norm branch and uniform smoothing error really imply existence of a
minimum in finite dimensions (or, more generally, a proper normed space). -/
theorem smoothed_hard_exists_minimizer [ProperSpace E]
    (z : Fin M → E →L[ℝ] ℝ) (δ μ η r : ℝ) (hμ : 0 < μ)
    (s : E → ℝ) (hs : Continuous s)
    (herror : ∀ x, |s x - hardFunction z δ r x| ≤ η) :
    ∃ y : E, ∀ x : E, s y / μ ≤ s x / μ := by
  let a : ℝ := max 0 (hardConstant M δ r + η + s 0) + 1
  have ha : 0 ≤ a := by dsimp [a]; have := le_max_left (0 : ℝ) (hardConstant M δ r + η + s 0); linarith
  obtain ⟨y, hy, hmin⟩ := (isCompact_closedBall (0 : E) a).exists_isMinOn
    ⟨0, by simpa using ha⟩ hs.continuousOn
  refine ⟨y, fun x => (div_le_div_iff_of_pos_right hμ).mpr ?_⟩
  by_cases hx : x ∈ Metric.closedBall (0 : E) a
  · exact hmin hx
  · have h0 : (0 : E) ∈ Metric.closedBall (0 : E) a := by simpa using ha
    have hy0 : s y ≤ s 0 := hmin h0
    have hxnorm : a < ‖x‖ := by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx
    have ha' : hardConstant M δ r + η + s 0 < a := by
      dsimp [a]
      have := le_max_right (0 : ℝ) (hardConstant M δ r + η + s 0)
      linarith
    have hnorm := hardFunction_norm_lower z δ r x
    have herr := (abs_le.mp (herror x)).1
    linarith

/-- The radius of a genuine minimizer is below two. -/
theorem normalized_minimizer_radius
    (z : Fin M → E →L[ℝ] ℝ) (δ μ η r ζ : ℝ)
    (hδ : 0 < δ) (hμ : 0 < μ) (hr0 : 0 ≤ r)
    (hr : r ≤ δ / 8) (hMδ : M * δ ≤ μ * ζ)
    (hη : η ≤ μ * ζ / 4) (hsmall : 4 * μ * ζ ≤ 1)
    (s : E → ℝ) (hs : ConvexOn ℝ univ s)
    (herror : ∀ x, |s x - hardFunction z δ r x| ≤ η)
    (y : E) (hy : ∀ x, s y / μ ≤ s x / μ)
    (hd : DifferentiableAt ℝ (fun x => s x / μ) y) : ‖y‖ < 2 := by
  have hmin : IsLocalMin (fun x => s x / μ) y := Filter.Eventually.of_forall hy
  have hz := hmin.hasFDerivAt_eq_zero hd.hasFDerivAt
  have hl := hard_family_localization z δ μ η r hδ hμ hr0 s hs herror y _ hd.hasFDerivAt
  rw [hz] at hl
  simp only [norm_zero, mul_zero, sub_zero, one_mul] at hl
  have hc := normalized_constant_bound (M := M) δ μ η r ζ hδ hr hMδ hη hsmall
  linarith

/-- The gradient-to-objective reduction after both points are localized.
The bound is valid for every comparison point in the radius-four ball. -/
theorem normalized_objective_reduction {f : E → ℝ}
    (hc : ConvexOn ℝ univ f) (x y : E) (g : E →L[ℝ] ℝ)
    (hd : HasFDerivAt f g x) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (hx : ‖x‖ ≤ 4) (hy : ‖y‖ ≤ 4) (hg : ‖g‖ ≤ ζ / 8) :
    f x - f y ≤ ζ := by
  have hdist : ‖x - y‖ ≤ 8 := by
    have := norm_sub_le x y
    linarith
  calc
    f x - f y ≤ ‖g‖ * ‖x - y‖ := convex_objective_gap hc hd y
    _ ≤ (ζ / 8) * 8 := mul_le_mul hg hdist (norm_nonneg _) (by positivity)
    _ = ζ := by ring

/-- The small normalized gradient demanded by the reduction automatically
satisfies the threshold in Lemma 6.2. -/
theorem normalized_gradient_bootstrap (μ ζ : ℝ) (hμ : 0 ≤ μ)
    (hsmall : 4 * μ * ζ ≤ 1) (g : E →L[ℝ] ℝ)
    (hg : ‖g‖ ≤ ζ / 8) : μ * ‖g‖ ≤ 1 / 32 := by
  have := mul_le_mul_of_nonneg_left hg hμ
  nlinarith

/-- The complete normalized analytic reduction used in the proof of
Corollary 1.3: a minimizer exists in radius two, and every output with
normalized gradient at most `ζ / 8` lies in radius four and has objective
gap at most `ζ`.  None of these conclusions is a premise. -/
theorem normalized_hard_family_reduction [ProperSpace E]
    (z : Fin M → E →L[ℝ] ℝ) (δ μ η r ζ : ℝ)
    (hδ : 0 < δ) (hμ : 0 < μ) (hζ : 0 ≤ ζ) (hr0 : 0 ≤ r)
    (hr : r ≤ δ / 8) (hMδ : M * δ ≤ μ * ζ)
    (hη : η ≤ μ * ζ / 4) (hsmall : 4 * μ * ζ ≤ 1)
    (s : E → ℝ) (hs : ConvexOn ℝ univ s) (hsd : Differentiable ℝ s)
    (herror : ∀ x, |s x - hardFunction z δ r x| ≤ η) :
    ∃ y : E, (∀ x, s y / μ ≤ s x / μ) ∧ ‖y‖ < 2 ∧
      ∀ (x : E) (g : E →L[ℝ] ℝ),
        HasFDerivAt (fun t => s t / μ) g x → ‖g‖ ≤ ζ / 8 →
        ‖x‖ < 4 ∧ s x / μ - s y / μ ≤ ζ := by
  obtain ⟨y, hy⟩ := smoothed_hard_exists_minimizer z δ μ η r hμ s hsd.continuous herror
  have hyr := normalized_minimizer_radius z δ μ η r ζ hδ hμ hr0 hr hMδ hη hsmall
    s hs herror y hy (by simpa only [div_eq_mul_inv] using (hsd y).mul_const μ⁻¹)
  refine ⟨y, hy, hyr, ?_⟩
  intro x g hd hg
  have hb := normalized_gradient_bootstrap μ ζ hμ.le hsmall g hg
  have hxr := normalized_output_radius z δ μ η r ζ hδ hμ hr0 hr hMδ hη hsmall
    s hs herror x g hd (by linarith)
  refine ⟨hxr, ?_⟩
  have hc : ConvexOn ℝ univ (fun t => s t / μ) := by
    simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using
      ConvexOn.smul (inv_nonneg.mpr hμ.le) hs
  exact normalized_objective_reduction hc x y g hd ζ hζ hxr.le (by linarith) hg

end HardFamily

section Rescaling

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Equation (6.7), with the origin as starting point. -/
noncomputable def rescaledHardObjective (L R κ : ℝ) (F : E → ℝ) (x : E) : ℝ :=
  (L * R ^ κ / (4 : ℝ) ^ κ) * F ((4 / R) • x)

/-- The gradient coefficient in the rescaled instance. -/
noncomputable def rescaledGradientCoefficient (L R κ : ℝ) : ℝ :=
  L * R ^ (κ - 1) / (4 : ℝ) ^ (κ - 1)

/-- The normalized objective target in equation (6.7). -/
noncomputable def normalizedObjectiveTarget (L R κ ε : ℝ) : ℝ :=
  2 * (4 : ℝ) ^ κ * ε / (L * R ^ (κ - 1))

lemma rescaling_coefficient_identity (L R κ : ℝ) (hR : 0 < R) :
    (L * R ^ κ / (4 : ℝ) ^ κ) * (4 / R) =
      rescaledGradientCoefficient L R κ := by
  unfold rescaledGradientCoefficient
  rw [Real.rpow_sub_one hR.ne', Real.rpow_sub_one (by norm_num : (4 : ℝ) ≠ 0)]
  field_simp

lemma rescaledGradientCoefficient_pos (L R κ : ℝ) (hL : 0 < L) (hR : 0 < R) :
    0 < rescaledGradientCoefficient L R κ := by
  unfold rescaledGradientCoefficient
  exact div_pos (mul_pos hL (Real.rpow_pos_of_pos hR _))
    (Real.rpow_pos_of_pos (by norm_num) _)

/-- Chain rule gives precisely the published gradient scaling, represented
as multiplication of the dual derivative by its positive coefficient. -/
theorem rescaled_hard_hasFDerivAt (L R κ : ℝ) (hR : 0 < R)
    (F : E → ℝ) (x : E) (g : E →L[ℝ] ℝ)
    (hd : HasFDerivAt F g ((4 / R) • x)) :
    HasFDerivAt (rescaledHardObjective L R κ F)
      (rescaledGradientCoefficient L R κ • g) x := by
  have hid : HasFDerivAt (fun t : E => (4 / R) • t)
      ((4 / R) • ContinuousLinearMap.id ℝ E) x :=
    (hasFDerivAt_id (𝕜 := ℝ) x).const_smul (4 / R)
  have hcomp := (hd.comp x hid).const_smul (L * R ^ κ / (4 : ℝ) ^ κ)
  have he : (L * R ^ κ / (4 : ℝ) ^ κ) •
      (g.comp ((4 / R) • ContinuousLinearMap.id ℝ E)) =
      rescaledGradientCoefficient L R κ • g := by
    rw [← rescaling_coefficient_identity L R κ hR]
    ext v
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, map_smul, smul_smul]
  simpa only [rescaledHardObjective, Pi.smul_apply, id_eq, Function.comp_def, smul_eq_mul, he] using hcomp

/-- Multiplication by the spatial scale exactly cancels the normalized
Hölder constant. -/
lemma rescaling_holder_coefficient (L R κ : ℝ) (hR : 0 < R) :
    rescaledGradientCoefficient L R κ * (4 / R) ^ (κ - 1) = L := by
  unfold rescaledGradientCoefficient
  rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 4) hR.le]
  have hRp := (Real.rpow_pos_of_pos hR (κ - 1)).ne'
  have h4p := (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 4) (κ - 1)).ne'
  field_simp

/-- The normalized Hölder gradient inequality is transported to exactly
constant `L`, as asserted after (6.7). -/
theorem rescaled_holder_gradient (L R κ : ℝ) (hL : 0 < L) (hR : 0 < R)
    (G : E → E →L[ℝ] ℝ)
    (hG : ∀ x y, ‖G x - G y‖ ≤ ‖x - y‖ ^ (κ - 1)) (x y : E) :
    ‖rescaledGradientCoefficient L R κ • G ((4 / R) • x) -
        rescaledGradientCoefficient L R κ • G ((4 / R) • y)‖ ≤
      L * ‖x - y‖ ^ (κ - 1) := by
  have hc := rescaledGradientCoefficient_pos L R κ hL hR
  have hb : 0 < (4 : ℝ) / R := div_pos (by norm_num) hR
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
  have hh := hG ((4 / R) • x) ((4 / R) • y)
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hb,
    Real.mul_rpow hb.le (norm_nonneg _)] at hh
  calc
    rescaledGradientCoefficient L R κ *
        ‖G ((4 / R) • x) - G ((4 / R) • y)‖ ≤
      rescaledGradientCoefficient L R κ *
        ((4 / R) ^ (κ - 1) * ‖x - y‖ ^ (κ - 1)) :=
      mul_le_mul_of_nonneg_left hh hc.le
    _ = L * ‖x - y‖ ^ (κ - 1) := by
      rw [← mul_assoc, rescaling_holder_coefficient L R κ hR]

lemma normalized_target_gradient_identity (L R κ ε : ℝ) (hL : 0 < L) (hR : 0 < R) :
    rescaledGradientCoefficient L R κ * (normalizedObjectiveTarget L R κ ε / 8) = ε := by
  unfold rescaledGradientCoefficient normalizedObjectiveTarget
  rw [Real.rpow_sub_one (by norm_num : (4 : ℝ) ≠ 0)]
  have hRp := (Real.rpow_pos_of_pos hR (κ - 1)).ne'
  have h4p := (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 4) κ).ne'
  field_simp
  ring

/-- The normalized target is positive in the nontrivial source regime. -/
lemma normalizedObjectiveTarget_pos (L R κ ε : ℝ)
    (hL : 0 < L) (hR : 0 < R) (hε : 0 < ε) :
    0 < normalizedObjectiveTarget L R κ ε := by
  unfold normalizedObjectiveTarget
  positivity

/-- The objective-error target rescales to exactly `2 ε R`, as used at the
end of the proof of Corollary 1.3. -/
lemma normalized_target_objective_identity (L R κ ε : ℝ) (hL : 0 < L) (hR : 0 < R) :
    (L * R ^ κ / (4 : ℝ) ^ κ) * normalizedObjectiveTarget L R κ ε = 2 * ε * R := by
  unfold normalizedObjectiveTarget
  rw [Real.rpow_sub_one hR.ne']
  have hRp := (Real.rpow_pos_of_pos hR κ).ne'
  have h4p := (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 4) κ).ne'
  field_simp

/-- A small gradient of the rescaled objective really yields the normalized
`ζ / 8` bound; the conclusion is deduced by derivative uniqueness and the
positive scaling identity. -/
theorem rescaled_small_gradient (L R κ ε : ℝ) (hL : 0 < L) (hR : 0 < R)
    (F : E → ℝ) (x : E) (g ĝ : E →L[ℝ] ℝ)
    (hd : HasFDerivAt F g ((4 / R) • x))
    (hhat : HasFDerivAt (rescaledHardObjective L R κ F) ĝ x)
    (hg : ‖ĝ‖ ≤ ε) : ‖g‖ ≤ normalizedObjectiveTarget L R κ ε / 8 := by
  have he := hhat.unique (rescaled_hard_hasFDerivAt L R κ hR F x g hd)
  have hc := rescaledGradientCoefficient_pos L R κ hL hR
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hc] at hg
  apply (mul_le_mul_iff_right₀ hc).mp
  rw [normalized_target_gradient_identity L R κ ε hL hR]
  exact hg

/-- Radius-four normalized points scale into the promised radius `R`. -/
theorem rescaled_radius (R : ℝ) (hR : 0 ≤ R) (y : E) (hy : ‖y‖ ≤ 4) :
    ‖(R / 4) • y‖ ≤ R := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ R / 4)]
  nlinarith

/-- Convexity is preserved by the actual positive objective/spatial
rescaling, so the rescaled hard function belongs to the convex class. -/
theorem rescaled_hard_convex (L R κ : ℝ) (hL : 0 < L) (hR : 0 < R)
    (F : E → ℝ) (hF : ConvexOn ℝ univ F) :
    ConvexOn ℝ univ (rescaledHardObjective L R κ F) := by
  let l : E →ₗ[ℝ] E := (4 / R) • LinearMap.id
  have hh : ConvexOn ℝ univ (fun x : E => F ((4 / R) • x)) := by
    simpa only [preimage_univ, Function.comp_def, l, LinearMap.smul_apply,
      LinearMap.id_apply] using hF.comp_linearMap l
  have ha : 0 ≤ L * R ^ κ / (4 : ℝ) ^ κ := by positivity
  simpa only [rescaledHardObjective, smul_eq_mul] using ConvexOn.smul ha hh

/-- A normalized minimizer gives an actual minimizer of the rescaled
objective in the required initial-radius ball. -/
theorem rescaled_minimizer (L R κ : ℝ) (hL : 0 < L) (hR : 0 < R)
    (F : E → ℝ) (y : E) (hy : ∀ x, F y ≤ F x) (hyr : ‖y‖ ≤ 4) :
    (∀ x, rescaledHardObjective L R κ F ((R / 4) • y) ≤
      rescaledHardObjective L R κ F x) ∧ ‖(R / 4) • y‖ ≤ R := by
  refine ⟨?_, rescaled_radius R hR.le y hyr⟩
  intro x
  unfold rescaledHardObjective
  have hb : (4 / R) * (R / 4) = (1 : ℝ) := by field_simp
  rw [smul_smul, hb, one_smul]
  exact mul_le_mul_of_nonneg_left (hy _) (by positivity)

end Rescaling

end P31
