import Paper28.RectifiableCalculusInput

/-! Lemma 2.1: complete n-Jacobian inequality, including all zero strata.
The paper-owned estimate is proved here from the classical Fischer matrix
input and the separately disclosed generic rectifiable-current calculus API.
No input contains the desired joint inequality or any free-product result. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open WithLp MeasureTheory
open scoped InnerProductSpace
universe u v

section FoldingMaps
variable {A B : Type u} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B]

/-- The smooth extension of a folding on its zero folded-block stratum. -/
def retainedNormFold : WithLp 2 (A × B) →L[ℝ] WithLp 2 (A × ℝ) :=
  (prodContinuousLinearEquiv 2 ℝ A ℝ).symm.toContinuousLinearMap.comp
    ((lpFst : WithLp 2 (A × B) →L[ℝ] A).prod 0)

theorem normFold_eq_retained (x : WithLp 2 (A × B)) (hx : x.snd = 0) :
    normFold x = retainedNormFold x := by
  simp [normFold, retainedNormFold, lpFst, hx]

theorem normFoldDerivative_eq_retained (x : WithLp 2 (A × B)) (hx : x.snd = 0)
    (w : WithLp 2 (A × B)) : normFoldDerivative x w = retainedNormFold w := by
  rw [normFoldDerivative_apply]
  simp [hx, retainedNormFold, lpFst]

theorem normFold_hasLipschitzConstant :
    HasLipschitzConstant (normFold : WithLp 2 (A × B) → WithLp 2 (A × ℝ)) := by
  refine ⟨1, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  simpa using normFold_dist x y

end FoldingMaps

section SphereCurrents
variable {H₁ H₂ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
  [FiniteDimensional ℝ H₁] [FiniteDimensional ℝ H₂]
  [MeasurableSpace (Triple H₁ H₂)]
variable (I : RectifiableSphereCalculusInput.{u,v} (Triple H₁ H₂))

/-- The smooth extension of the right folding on its zero folded block. -/
def retainedRightFold : Triple H₁ H₂ →L[ℝ] WithLp 2 (H₂ × ℝ) :=
  retainedNormFold.comp reverseTripleIsometry.toContinuousLinearMap

theorem rightFold_hasLipschitzConstant :
    HasLipschitzConstant (rightFold : Triple H₁ H₂ → WithLp 2 (H₂ × ℝ)) := by
  refine ⟨1, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  have h := normFold_dist (reverseTriple x) (reverseTriple y)
  have hd : dist (reverseTriple x) (reverseTriple y) = dist x y :=
    (reverseTripleIsometry (H₁ := H₁) (H₂ := H₂)).isometry.dist_eq x y
  simpa using h.trans_eq hd

/-- The approximate tangential differential of L is the actual explicitly
computed operator on every stratum, including the zero folded block. -/
theorem leftFold_approx_differential_ae {n : ℕ} (C : I.Current n) :
    ∀ᵐ x ∂I.massMeasure C, ∀ w : I.plane C x,
      I.approxDifferential leftFold C x w = normFoldDerivative x w.val := by
  apply approximate_differential_piecewise_ae I leftFold normFold_hasLipschitzConstant
    retainedNormFold normFoldDerivative (fun x => x.snd ≠ 0)
  · intro x hx
    exact hasFDerivAt_leftFold x hx
  · intro x hx
    exact normFold_eq_retained x (not_ne_iff.mp hx)
  · intro x hx w
    exact normFoldDerivative_eq_retained x (not_ne_iff.mp hx) w

/-- The right-folding version of the same derived identification. -/
theorem rightFold_approx_differential_ae {n : ℕ} (C : I.Current n) :
    ∀ᵐ x ∂I.massMeasure C, ∀ w : I.plane C x,
      I.approxDifferential rightFold C x w = rightFoldDerivative x w.val := by
  apply approximate_differential_piecewise_ae I rightFold rightFold_hasLipschitzConstant
    retainedRightFold rightFoldDerivative (fun x => (reverseTriple x).snd ≠ 0)
  · intro x hx
    exact hasFDerivAt_rightFold x hx
  · intro x hx
    exact normFold_eq_retained (reverseTriple x) (not_ne_iff.mp hx)
  · intro x hx w
    exact normFoldDerivative_eq_retained (reverseTriple x) (not_ne_iff.mp hx) (reverseTriple w)

/-- Lemma 2.1, with its original dimension threshold and almost-everywhere
quantifier. The only hypotheses beyond finite-dimensional real Hilbert spaces
are the disclosed, generic published external inputs. -/
theorem lemma_2_1 (hFischer : FischerInput) (n : ℕ) (hn : 4 ≤ n) (C : I.Current n) :
    ∀ᵐ x ∂I.massMeasure C,
      currentJacobian I leftFold C x + currentJacobian I rightFold C x ≤ 1 := by
  let Pₗ : Triple H₁ H₂ →L[ℝ] WithLp 2 (ℝ × H₂) := lpSnd
  let Pᵣ : Triple H₁ H₂ →L[ℝ] WithLp 2 (ℝ × H₁) :=
    (lpSnd : Triple H₂ H₁ →L[ℝ] WithLp 2 (ℝ × H₁)).comp reverseTripleIsometry.toContinuousLinearMap
  filter_upwards [I.dimension_ae C, I.tangent_ae C,
    linear_kernel_tangent_ae I Pₗ C, linear_kernel_tangent_ae I Pᵣ C,
    leftFold_approx_differential_ae I C, rightFold_approx_differential_ae I C]
    with x hdim htan hkerL hkerR hDL hDR
  have heqL : I.approxDifferential leftFold C x =
      (fun w : I.plane C x => normFoldDerivative x w.val) := funext hDL
  have heqR : I.approxDifferential rightFold C x =
      (fun w : I.plane C x => rightFoldDerivative x w.val) := funext hDR
  unfold currentJacobian
  rw [heqL, heqR]
  apply two_foldings_nJacobian_stratified hFischer x (I.plane C x) (by omega) htan
  · intro hx w
    exact hkerL hx w
  · intro hx w
    exact hkerR hx w

end SphereCurrents
end Paper28
