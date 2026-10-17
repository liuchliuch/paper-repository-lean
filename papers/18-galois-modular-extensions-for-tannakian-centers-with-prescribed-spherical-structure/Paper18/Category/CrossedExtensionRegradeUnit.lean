import Paper18.Category.CrossedExtensionRegrade

/-! # The actual unit comparison for degree regrading -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
namespace Paper18.Category.CrossedExtension
variable {A : Type} [Fintype A] [AddGroup A]

lemma gradingUnit_isZero (a : A) (ha : a ≠ 0) :
    IsZero ((𝟙_ (PointedVec A)) a) :=
  (GradedObject.isInitialSingleObjApply 0 (𝟙_ (FGModuleCat ℂ)) a ha).isZero

/-- The actual unit comparison is canonical in degree zero and the unique
isomorphism between zero objects in every other degree. -/
def regradeUnitIso (e : A ≃+ A) :
    𝟙_ (PointedVec A) ≅ (regradeFunctor e).obj (𝟙_ (PointedVec A)) :=
  GradedObject.isoMk _ _ (fun a => by
    by_cases ha : a = 0
    · subst a
      exact eqToIso (congrArg (𝟙_ (PointedVec A)) e.map_zero.symm)
    · have hea : e a ≠ 0 := by
        intro h
        exact ha (e.injective (h.trans e.map_zero.symm))
      exact (gradingUnit_isZero a ha).iso (gradingUnit_isZero (e a) hea))

@[simp] lemma regradeUnitIso_hom_zero (e : A ≃+ A) :
    (regradeUnitIso e).hom 0 =
      eqToHom (congrArg (𝟙_ (PointedVec A)) e.map_zero.symm) := by
  simp [regradeUnitIso]

@[simp] lemma regradeUnitIso_inv_zero (e : A ≃+ A) :
    (regradeUnitIso e).inv 0 =
      eqToHom (congrArg (𝟙_ (PointedVec A)) e.map_zero) := by
  simp [regradeUnitIso]

end Paper18.Category.CrossedExtension
