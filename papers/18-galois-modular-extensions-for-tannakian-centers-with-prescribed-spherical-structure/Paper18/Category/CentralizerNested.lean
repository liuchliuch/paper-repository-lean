import Paper18.Category.FusionSubcategoryFunctor
import Paper18.Category.CentralizerFusion
import Paper18.Category.RelativeTensorCentralDimensionBasic

/-! # Actual nested centralizers and the ambient union centralizer -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category.CentralizerNested
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  (B : Set C) (e : CentralizerCategory B)

lemma forward_property (X : CentralizerCategory ({e} : Set (CentralizerCategory B))) :
    X.obj.obj ∈ centralizer (B ∪ {e.obj}) := by
  intro Y hY
  rcases hY with hY | hY
  · exact X.obj.property Y hY
  · rcases Set.mem_singleton_iff.mp hY with rfl
    exact (X.property e (Set.mem_singleton e)).map (centralizerInclusion B)

/-- The actual forgetful restriction retains the two centralization conditions. -/
def forward : CentralizerCategory ({e} : Set (CentralizerCategory B)) ⥤
    CentralizerCategory (B ∪ {e.obj}) :=
  fullSubcategoryLift (centralizerProperty (B ∪ {e.obj}))
    (centralizerInclusion ({e} : Set (CentralizerCategory B)) ⋙ centralizerInclusion B)
    (forward_property B e)

def inverseBase : CentralizerCategory (B ∪ {e.obj}) ⥤ CentralizerCategory B :=
  fullSubcategoryLift (centralizerProperty B) (centralizerInclusion (B ∪ {e.obj}))
    (fun X Y hY => X.property Y (Or.inl hY))

lemma inverse_property (X : CentralizerCategory (B ∪ {e.obj})) :
    (inverseBase B e).obj X ∈ centralizer ({e} : Set (CentralizerCategory B)) := by
  intro Y hY
  have hYe : Y = e := Set.mem_singleton_iff.mp hY
  subst Y
  apply (centralizes_map_iff (centralizerInclusion B) _ _).mp
  exact X.property e.obj (Or.inr (Set.mem_singleton e.obj))

def inverse : CentralizerCategory (B ∪ {e.obj}) ⥤
    CentralizerCategory ({e} : Set (CentralizerCategory B)) :=
  fullSubcategoryLift (centralizerProperty ({e} : Set (CentralizerCategory B)))
    (inverseBase B e) (inverse_property B e)

instance forward_braided : (forward B e).Braided := by unfold forward; infer_instance
instance forward_additive : (forward B e).Additive := by unfold forward; infer_instance
instance forward_linear : (forward B e).Linear ℂ := by unfold forward; infer_instance
instance forward_full : (forward B e).Full := by unfold forward; infer_instance
instance forward_faithful : (forward B e).Faithful := by unfold forward; infer_instance
instance inverseBase_braided : (inverseBase B e).Braided := by unfold inverseBase; infer_instance
instance inverseBase_additive : (inverseBase B e).Additive := by unfold inverseBase; infer_instance
instance inverseBase_linear : (inverseBase B e).Linear ℂ := by unfold inverseBase; infer_instance
instance inverse_braided : (inverse B e).Braided := by unfold inverse; infer_instance
instance inverse_additive : (inverse B e).Additive := by unfold inverse; infer_instance
instance inverse_linear : (inverse B e).Linear ℂ := by unfold inverse; infer_instance

/-- The actual nested full category and ambient union full category are
equivalent by their identical underlying objects and morphisms. -/
def equivalence : CentralizerCategory ({e} : Set (CentralizerCategory B)) ≌
    CentralizerCategory (B ∪ {e.obj}) where
  functor := forward B e
  inverse := inverse B e
  unitIso := NatIso.ofComponents (fun X => Iso.refl X)
    (fun f => by change f ≫ 𝟙 _ = 𝟙 _ ≫ f; simp)
  counitIso := NatIso.ofComponents (fun X => Iso.refl X)
    (fun f => by change f ≫ 𝟙 _ = 𝟙 _ ≫ f; simp)

section Integral
variable [HasKernels C] [HasFiniteBiproducts C] [RightRigidCategory C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

/-- Integrality in an actual centralizer can be checked in the actual
ambient simultaneous centralizer. No numerical FP compatibility is assumed. -/
theorem integral_of_ambient_union_integral
    (hI : S.CentralizerIntegral (B ∪ {e.obj})) :
    letI := S.fullSubcategoryHasKernels (centralizerProperty B)
    letI := S.fullSubcategoryRightRigid (centralizerProperty B)
    letI := S.fullSubcategorySimpleUnit (centralizerProperty B)
    (S.centralizerSkeleton B).CentralizerIntegral {e} := by
  letI := S.fullSubcategoryHasKernels (centralizerProperty B)
  letI := S.fullSubcategoryRightRigid (centralizerProperty B)
  letI := S.fullSubcategorySimpleUnit (centralizerProperty B)
  let T := S.centralizerSkeleton B
  let P := centralizerProperty ({e} : Set (CentralizerCategory B))
  let Q := centralizerProperty (B ∪ {e.obj})
  letI := T.fullSubcategoryHasKernels P
  letI := T.fullSubcategoryRightRigid P
  letI := T.fullSubcategorySimpleUnit P
  letI := S.fullSubcategoryHasKernels Q
  letI := S.fullSubcategoryRightRigid Q
  letI := S.fullSubcategorySimpleUnit Q
  exact (T.fullSubcategorySkeleton P).integral_of_integral_target
    (S.fullSubcategorySkeleton Q) (forward B e) hI

end Integral
end Paper18.Category.CentralizerNested
