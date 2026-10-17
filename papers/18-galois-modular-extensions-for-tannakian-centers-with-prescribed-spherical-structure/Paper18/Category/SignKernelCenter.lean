import Paper18.Category.SignKernelDimensions

/-! # Restricting the actual sign kernel to the actual transparent center -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
universe v u w
namespace Paper18.Category.SignKernel
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  (χ : 𝟭 C ≅ 𝟭 C) [NatTrans.IsMonoidal χ.hom]

/-- The actual character restricts to every actual full tensor subcategory. -/
def restrict (P : ObjectProperty C) [P.IsMonoidal] :
    𝟭 P.FullSubcategory ≅ 𝟭 P.FullSubcategory where
  hom := { app X := χ.hom.app X.obj
           naturality _ _ f := χ.hom.naturality f }
  inv := { app X := χ.inv.app X.obj
           naturality _ _ f := χ.inv.naturality f }
  hom_inv_id := by ext X; exact χ.hom_inv_id_app X.obj
  inv_hom_id := by ext X; exact χ.inv_hom_id_app X.obj

instance restrict_monoidal (P : ObjectProperty C) [P.IsMonoidal] :
    (restrict χ P).hom.IsMonoidal where
  unit := by
    change 𝟙 (𝟙_ C) ≫ χ.hom.app (𝟙_ C) = 𝟙 (𝟙_ C)
    rw [TensorAutomorphism.unit_component, Category.id_comp]
  tensor X Y := by
    change 𝟙 _ ≫ χ.hom.app (X.obj ⊗ Y.obj) =
      (χ.hom.app X.obj ⊗ₘ χ.hom.app Y.obj) ≫ 𝟙 _
    rw [TensorAutomorphism.tensor_component, Category.id_comp, Category.comp_id]

omit [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [NatTrans.IsMonoidal χ.hom] in
lemma restrict_involutive (hχ : ∀ X : C, χ.hom.app X ≫ χ.hom.app X = 𝟙 X)
    (P : ObjectProperty C) [P.IsMonoidal] (X : P.FullSubcategory) :
    (restrict χ P).hom.app X ≫ (restrict χ P).hom.app X = 𝟙 X := hχ X.obj

omit [MonoidalPreadditive C] [MonoidalLinear ℂ C] [NatTrans.IsMonoidal χ.hom] in
@[simp] lemma restrict_positive (P : ObjectProperty C) [P.IsMonoidal] (X : P.FullSubcategory) :
    positiveProperty (restrict χ P) X ↔ positiveProperty χ X.obj := Iff.rfl

section Finite
attribute [local instance 2000] RightRigidCategory.rightDual
variable [HasFiniteBiproducts C] [HasKernels C] [RightRigidCategory C]
  [Simple (𝟙_ C)] [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

omit [NatTrans.IsMonoidal χ.hom] in
lemma supportFPdim_restrict (P : ObjectProperty C) [IsAdditiveFullProperty P] [P.IsMonoidal] :
    (letI := S.fullSubcategoryHasKernels P
     letI := S.fullSubcategoryRightRigid P
     letI := S.fullSubcategorySimpleUnit P
     (S.fullSubcategorySkeleton P).supportFPdim (positiveProperty (restrict χ P))) =
      S.supportFPdim (fun X => P X ∧ positiveProperty χ X) := by
  letI := S.fullSubcategoryHasKernels P
  letI := S.fullSubcategoryRightRigid P
  letI := S.fullSubcategorySimpleUnit P
  let T := S.fullSubcategorySkeleton P
  have hd (i : {i : ι // P (S.simpleObject i)}) :
      T.fusionBasis.fpdim i = S.fusionBasis.fpdim i.val := by
    rw [← T.fpdim_simple]
    exact (S.fullSubcategoryFPdim_eq P (T.simpleObject i)).trans (S.fpdim_simple i.val)
  change (∑ i : {i : ι // P (S.simpleObject i)},
      if positiveProperty χ (S.simpleObject i.val) then T.fusionBasis.fpdim i ^ 2 else 0) = _
  simp_rw [hd]
  unfold FiniteSemisimpleSkeleton.supportFPdim
  dsimp only
  calc
    _ = ∑ i ∈ Finset.univ.filter (fun i => P (S.simpleObject i)),
        if positiveProperty χ (S.simpleObject i) then S.fusionBasis.fpdim i ^ 2 else 0 :=
      (Finset.sum_subtype (Finset.univ.filter (fun i => P (S.simpleObject i)))
        (fun i => by simp) (fun i =>
          if positiveProperty χ (S.simpleObject i) then S.fusionBasis.fpdim i ^ 2 else 0)).symm
    _ = _ := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hp : P (S.simpleObject i) <;> simp [hp]

variable [BraidedCategory C]
  (hχ : ∀ X : C, χ.hom.app X ≫ χ.hom.app X = 𝟙 X)

include hχ in
/-- Nontriviality on the actual center is witnessed by an actual transparent
negative simple from an actual decomposition. -/
lemma negative_transparent_simple (X : C) (hZ : X ∈ mugerCenter)
    (hX : χ.hom.app X ≠ 𝟙 X) :
    ∃ i, S.simpleObject i ∈ mugerCenter ∧ χ.hom.app (S.simpleObject i) = -𝟙 _ := by
  obtain ⟨a, ha⟩ := exists_negative_label S χ hχ X hX
  exact ⟨S.label X a, S.property_label (centralizerProperty (Set.univ : Set C))
    (⟨X, hZ⟩ : CentralizerCategory (Set.univ : Set C)) a, ha⟩

include hχ in
/-- The restriction of a nontrivial involutive tensor character to the
actual Müger center has index two, measured by its actual simple supports. -/
theorem center_restriction_indexTwo (X : C) (hZ : X ∈ mugerCenter)
    (hX : χ.hom.app X ≠ 𝟙 X) :
    S.supportFPdim (centralizerProperty (Set.univ : Set C)) =
      2 * S.supportFPdim (fun Y => Y ∈ mugerCenter ∧ positiveProperty χ Y) := by
  let P := centralizerProperty (Set.univ : Set C)
  letI := S.fullSubcategoryHasKernels P
  letI := S.fullSubcategoryRightRigid P
  letI := S.fullSubcategorySimpleUnit P
  let T := S.fullSubcategorySkeleton P
  obtain ⟨i, hi, hneg⟩ := negative_transparent_simple χ S hχ X hZ hX
  let j : {i : ι // P (S.simpleObject i)} := ⟨i, hi⟩
  have hn : (restrict χ P).hom.app (T.simpleObject j) = -𝟙 _ := hneg
  have hd := supportFPdim_indexTwo T (restrict χ P) (restrict_involutive χ hχ P) j hn
  calc
    _ = T.fusionBasis.totalFPdim := (S.fullSubcategory_totalFPdim_eq P).symm
    _ = 2 * T.supportFPdim (positiveProperty (restrict χ P)) := hd
    _ = _ := by rw [supportFPdim_restrict χ S P]; rfl

end Finite
end Paper18.Category.SignKernel
