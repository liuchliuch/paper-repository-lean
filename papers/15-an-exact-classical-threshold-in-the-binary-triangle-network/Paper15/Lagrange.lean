import Paper15.ExceptionalValue
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Pi

/-! # Lagrange multipliers at an interior constrained local maximum -/
noncomputable section
namespace Paper15
abbrev SourceCoords := (Fin 3 → ℝ) × (Fin 3 → ℝ)

/-- The actual moment functions on the six-dimensional coordinate space. -/
def coordM (i : Fin 3) (p : SourceCoords) : ℝ :=
  if i = 0 then (momentsOf p.1 p.2).M1
  else if i = 1 then (momentsOf p.1 p.2).M2
  else (momentsOf p.1 p.2).M3

lemma contDiff_coordM (i : Fin 3) : ContDiff ℝ 1 (coordM i) := by
  unfold coordM
  fin_cases i <;>
    norm_num [momentsOf, m1Of, m2Of, m3Of, eQty, tQty, sQty, vQty, uOf] <;> fun_prop

lemma fderiv_coord_x (F : SourceCoords → ℝ) (x y : Fin 3 → ℝ)
    (hF : DifferentiableAt ℝ F (x,y)) (i : Fin 3) :
    (fderiv ℝ F (x,y)) (Pi.single i 1, 0) =
      deriv (fun r => F (Function.update x i r, y)) (x i) := by
  have hp : HasFDerivAt (fun r : ℝ => (Function.update x i r, y))
      ((ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ ℝ))).prod 0) (x i) :=
    (hasFDerivAt_update (𝕜 := ℝ) x (i := i) (x i)).prodMk (hasFDerivAt_const y (x i))
  have hF' : HasFDerivAt F (fderiv ℝ F (x,y)) (Function.update x i (x i),y) := by
    simpa using hF.hasFDerivAt
  have hd := hF'.comp (x i) hp
  have hs : ((ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ ℝ))) :
      ℝ →L[ℝ] (Fin 3 → ℝ)) (1 : ℝ) = (Pi.single i 1 : Fin 3 → ℝ) := by
    funext j
    by_cases hj : j = i
    · subst j; simp [ContinuousLinearMap.pi_apply]
    · simp [ContinuousLinearMap.pi_apply, Pi.single_apply, hj]
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    hs, ContinuousLinearMap.zero_apply, Function.comp_apply] using hd.hasDerivAt.deriv.symm

lemma fderiv_coord_y (F : SourceCoords → ℝ) (x y : Fin 3 → ℝ)
    (hF : DifferentiableAt ℝ F (x,y)) (i : Fin 3) :
    (fderiv ℝ F (x,y)) (0, Pi.single i 1) =
      deriv (fun r => F (x, Function.update y i r)) (y i) := by
  have hp : HasFDerivAt (fun r : ℝ => (x, Function.update y i r))
      ((0 : ℝ →L[ℝ] (Fin 3 → ℝ)).prod (ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ ℝ)))) (y i) :=
    (hasFDerivAt_const x (y i)).prodMk (hasFDerivAt_update (𝕜 := ℝ) y (i := i) (y i))
  have hF' : HasFDerivAt F (fderiv ℝ F (x,y)) (x,Function.update y i (y i)) := by
    simpa using hF.hasFDerivAt
  have hd := hF'.comp (y i) hp
  have hs : ((ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ ℝ))) :
      ℝ →L[ℝ] (Fin 3 → ℝ)) (1 : ℝ) = (Pi.single i 1 : Fin 3 → ℝ) := by
    funext j
    by_cases hj : j = i
    · subst j; simp [ContinuousLinearMap.pi_apply]
    · simp [ContinuousLinearMap.pi_apply, Pi.single_apply, hj]
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    hs, ContinuousLinearMap.zero_apply, Function.comp_apply] using hd.hasDerivAt.deriv.symm

/-- At a constrained local maximum, regularity provides the actual
Lagrangian stationarity condition used by Lemma 7. -/
theorem exceptional_stationary_of_localMax {x y : Fin 3 → ℝ}
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i)
    (hmax : IsLocalMaxOn (coordM 1)
      {p : SourceCoords | coordM 0 p = coordM 0 (x,y) ∧ coordM 2 p = coordM 2 (x,y)} (x,y)) :
    IsExceptionalStationary x y := by
  let f : Fin 2 → SourceCoords → ℝ := ![coordM 0, coordM 2]
  have hf (i : Fin 2) : HasStrictFDerivAt (f i) (fderiv ℝ (f i) (x,y)) (x,y) := by
    fin_cases i
    · exact (contDiff_coordM 0).hasStrictFDerivAt le_rfl
    · exact (contDiff_coordM 2).hasStrictFDerivAt le_rfl
  have hlevels : {p : SourceCoords | ∀ i : Fin 2, f i p = f i (x,y)} =
      {p : SourceCoords | coordM 0 p = coordM 0 (x,y) ∧ coordM 2 p = coordM 2 (x,y)} := by
    ext p
    simp [f, Fin.forall_fin_two]
  have hext : IsLocalExtrOn (coordM 1) {p | ∀ i : Fin 2, f i p = f i (x,y)} (x,y) := by
    rw [hlevels]
    exact hmax.isExtr
  obtain ⟨Λ, q, hne, hD⟩ := hext.exists_multipliers_of_hasStrictFDerivAt hf
    ((contDiff_coordM 1).hasStrictFDerivAt le_rfl)
  change (∑ i : Fin 2, Λ i • fderiv ℝ (f i) (x,y)) + q • fderiv ℝ (coordM 1) (x,y) = 0 at hD
  simp only [Fin.sum_univ_two, f, Matrix.cons_val_zero, Matrix.cons_val_one] at hD
  have diff (i : Fin 3) : DifferentiableAt ℝ (coordM i) (x,y) :=
    ((contDiff_coordM i).differentiable le_rfl).differentiableAt
  have hq : q ≠ 0 := by
    intro hq0
    have hcoe : Λ 0 ≠ 0 ∨ Λ 1 ≠ 0 := by
      by_contra h
      push_neg at h
      apply hne
      have hΛ : Λ = 0 := by funext i; fin_cases i <;> simp [h.1, h.2]
      simp [hΛ, hq0]
    apply lemma6_derivative_independent hx hy
    refine ⟨Λ 0, Λ 1, hcoe, ?_, ?_⟩
    · intro i
      have h := congrArg (fun L : SourceCoords →L[ℝ] ℝ => L (Pi.single i 1,0)) hD
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        smul_eq_mul, ContinuousLinearMap.zero_apply, hq0, zero_mul, add_zero] at h
      rw [fderiv_coord_x _ _ _ (diff 0), fderiv_coord_x _ _ _ (diff 2)] at h
      simpa [coordM] using h
    · intro i
      have h := congrArg (fun L : SourceCoords →L[ℝ] ℝ => L (0,Pi.single i 1)) hD
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        smul_eq_mul, ContinuousLinearMap.zero_apply, hq0, zero_mul, add_zero] at h
      rw [fderiv_coord_y _ _ _ (diff 0), fderiv_coord_y _ _ _ (diff 2)] at h
      simpa [coordM] using h
  let lam := -Λ 0 / q
  let mu := -Λ 1 / q
  let L : SourceCoords → ℝ := fun p => exceptionalLagrangian lam mu p.1 p.2
  have hL : DifferentiableAt ℝ L (x,y) := by
    dsimp [L, exceptionalLagrangian, momentsOf, m1Of, m2Of, m3Of, eQty, tQty, sQty, vQty, uOf]
    fun_prop
  have hDL : fderiv ℝ L (x,y) = 0 := by
    have hLF : L = fun p => coordM 1 p - lam * coordM 0 p - mu * coordM 2 p := rfl
    have hLf : HasFDerivAt L
        (fderiv ℝ (coordM 1) (x,y) - lam • fderiv ℝ (coordM 0) (x,y) -
          mu • fderiv ℝ (coordM 2) (x,y)) (x,y) := by
      rw [hLF]
      exact ((diff 1).hasFDerivAt.sub ((diff 0).hasFDerivAt.const_mul lam)).sub
        ((diff 2).hasFDerivAt.const_mul mu)
    rw [hLf.fderiv]
    apply ContinuousLinearMap.ext
    intro v
    have h := congrArg (fun D : SourceCoords →L[ℝ] ℝ => D v) hD
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, ContinuousLinearMap.zero_apply] at h
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, ContinuousLinearMap.zero_apply]
    dsimp [lam, mu]
    field_simp [hq]
    nlinarith
  refine ⟨lam, mu, ?_, ?_⟩
  · intro i
    have h := fderiv_coord_x L x y hL i
    rw [hDL] at h
    exact h.symm
  · intro i
    have h := fderiv_coord_y L x y hL i
    rw [hDL] at h
    exact h.symm

/-- An interior constrained local maximum of the exceptional table has value
`t_*`, with no stationarity or multiplier hypothesis left to supply. -/
theorem exceptional_localMax_value {x y : Fin 3 → ℝ}
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) (hz : ∀ i, x i + y i < 1)
    (h1 : (momentsOf x y).M1 = 0) (h3 : (momentsOf x y).M3 = 0)
    (hmax : IsLocalMaxOn (coordM 1)
      {p : SourceCoords | coordM 0 p = coordM 0 (x,y) ∧ coordM 2 p = coordM 2 (x,y)} (x,y)) :
    (momentsOf x y).M2 = tStar :=
  exceptional_stationary_value hx hy hz (exceptional_stationary_of_localMax hx hy hmax) h1 h3

end Paper15
