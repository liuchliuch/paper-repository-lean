import Paper35.GaussianSwitches

/-! Fixed endpoints have zero Gaussian Crofton measure. This is proved from
the ordinary unit-projection law, separately from the interior regularity input. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace Paper35.GaussianMarked

theorem fixed_projection_level_null (hproj : GaussianUnitProjectionLaw)
    {m : ℕ} (v : Source.Space m) (hv : ‖v‖ = 1) (a : ℝ) :
    standardGaussian m {D | inner ℝ D v = a} = 0 := by
  letI : NoAtoms (gaussianReal 0 1) := noAtoms_gaussianReal (by norm_num)
  have h := congrArg (fun μ : Measure ℝ => μ {a}) (hproj m v hv)
  dsimp only at h
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton a)] at h
  simpa only [Set.preimage_setOf_eq, Set.mem_singleton_iff, measure_singleton] using h

/-- The two endpoints excluded from the parameter count in Lemma 6.1
almost surely do not lie on the sampled hyperplane. -/
theorem spherical_endpoints_null (hproj : GaussianUnitProjectionLaw)
    {m : ℕ} (ψ : ℝ → Source.Space m) (L : ℝ)
    (h0 : ‖ψ 0‖ = 1) (hL : ‖ψ L‖ = 1) :
    standardGaussian m {D | inner ℝ D (ψ 0) = 0 ∨ inner ℝ D (ψ L) = 0} = 0 := by
  apply le_antisymm _ (zero_le _)
  calc
    _ ≤ standardGaussian m {D | inner ℝ D (ψ 0) = 0} +
        standardGaussian m {D | inner ℝ D (ψ L) = 0} := measure_union_le _ _
    _ = 0 := by rw [fixed_projection_level_null hproj _ h0,
      fixed_projection_level_null hproj _ hL, add_zero]

theorem ae_spherical_endpoints_nonzero (hproj : GaussianUnitProjectionLaw)
    {m : ℕ} (ψ : ℝ → Source.Space m) (L : ℝ)
    (h0 : ‖ψ 0‖ = 1) (hL : ‖ψ L‖ = 1) :
    ∀ᵐ D ∂standardGaussian m, inner ℝ D (ψ 0) ≠ 0 ∧ inner ℝ D (ψ L) ≠ 0 := by
  simpa only [ae_iff, not_and_or, Classical.not_not] using
    spherical_endpoints_null hproj ψ L h0 hL

end Paper35.GaussianMarked
