import Paper18.Category.RepresentationRightTranslation

/-! # Actual averaging maps for the finite regular representation -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators MonObj
namespace Paper18.Category.Representation
variable {G : Type} [Group G] [Fintype G]

/-- Sum all coordinates of an actual function on the finite group. -/
def functionSumLinear : (G → ℂ) →ₗ[ℂ] ℂ := ∑ g : G, LinearMap.proj g

omit [Group G] in
@[simp]
theorem functionSumLinear_apply (f : G → ℂ) : functionSumLinear f = ∑ g, f g := by
  simp [functionSumLinear]

/-- The sum map is invariant under actual left translation. -/
def functionsSum : functions (G := G) ⟶ 𝟙_ (FDRep ℂ G) where
  hom := ModuleCat.ofHom functionSumLinear
  comm g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    change functionSumLinear (functionAction g f) = functionSumLinear f
    simp only [functionSumLinear_apply, functionAction_apply]
    apply Fintype.sum_equiv (Equiv.mulLeft g⁻¹)
    intro h
    rfl

/-- The ordinary mean is an actual map of representations. -/
def functionsAverage : functions (G := G) ⟶ 𝟙_ (FDRep ℂ G) :=
  (Fintype.card G : ℂ)⁻¹ • functionsSum

theorem functionsOne_sum :
    functionsOne (G := G) ≫ functionsSum = (Fintype.card G : ℂ) • 𝟙 _ := by
  apply Action.Hom.ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  change functionSumLinear (fun _ : G => (show ℂ from c)) =
    (Fintype.card G : ℂ) * (show ℂ from c)
  simp only [functionSumLinear_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The actual constant-function unit has an actual representation-linear
retraction, supplied by the finite-group mean. -/
@[reassoc (attr := simp)]
theorem functionsOne_average :
    functionsOne (G := G) ≫ functionsAverage = 𝟙 _ := by
  rw [functionsAverage, Linear.comp_smul, functionsOne_sum, smul_smul]
  have h : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp [h]

/-- Averaging the actual right translations is the constant-sum operator. -/
theorem sum_rightTranslation :
    (∑ g : G, rightTranslation g) = functionsSum ≫ functionsOne := by
  apply Action.Hom.ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  funext h
  change (((forget₂ (FDRep ℂ G) (FGModuleCat ℂ)).map
      (∑ g : G, rightTranslation g)).hom f) h = _
  rw [Functor.map_sum, ModuleCat.hom_sum]
  simp only [LinearMap.sum_apply]
  change ((∑ g : G, rightTranslationLinear g f) : G → ℂ) h = functionSumLinear f
  rw [Finset.sum_apply]
  change (∑ g : G, f (h * g)) = functionSumLinear f
  rw [functionSumLinear_apply]
  apply Fintype.sum_equiv (Equiv.mulLeft h)
  intro g
  rfl

/-- The invariant projector of the actual regular representation factors
through its actual trivial representation. -/
theorem average_rightTranslation :
    (Fintype.card G : ℂ)⁻¹ • (∑ g : G, rightTranslation g) =
      functionsAverage ≫ functionsOne := by
  rw [sum_rightTranslation, functionsAverage, Linear.smul_comp]

end Paper18.Category.Representation
