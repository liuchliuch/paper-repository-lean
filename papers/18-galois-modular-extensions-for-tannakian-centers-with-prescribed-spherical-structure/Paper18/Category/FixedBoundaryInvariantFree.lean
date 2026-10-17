import Paper18.Category.FixedBoundaryDescentAverage
import Paper18.Category.FixedBoundaryFreeComparison

/-! # Actual regular invariant maps for a staged tensor embedding

The finite-group averaging proof works on the actual carrier morphisms.
It therefore applies to the regular algebra first mapped into the
boundary and then into the extension, without changing its algebra data.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open scoped MonObj Obj
universe v u v' u'
namespace Paper18.Category.FixedBoundary
variable {G : Type} [Group G] [Fintype G]
  {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℂ A]
  [MonoidalCategory A] [BraidedCategory A]
  {N : Type u'} [Category.{v'} N] [Preadditive N] [Linear ℂ N]
  [MonoidalCategory N] [BraidedCategory N]
  [MonoidalPreadditive N] [MonoidalLinear ℂ N]
  [RightRigidCategory N] [Limits.HasCoequalizers N]
  (F0 : FDRep ℂ G ⥤ A) [F0.Braided] [F0.Additive] [F0.Linear ℂ]
  (i : A ⥤ N) [i.Braided] [i.Additive] [i.Linear ℂ]

local instance stagedImageMonObj : MonObj (i.obj (regularAlgebra F0)) :=
  Functor.monObjObj (F := i) (regularAlgebra F0)
local instance stagedImageCommMonObj : IsCommMonObj (i.obj (regularAlgebra F0)) :=
  Functor.isCommMonObj_obj

/-- The actual staged unit equals the raw composite regular unit. -/
theorem stagedRegular_unit :
    η[i.obj (regularAlgebra F0)] =
      Functor.LaxMonoidal.ε (F0 ⋙ i) ≫ (F0 ⋙ i).map Representation.functionsOne := by
  change Functor.LaxMonoidal.ε i ≫
      i.map (Functor.LaxMonoidal.ε F0 ≫ F0.map Representation.functionsOne) =
    (Functor.LaxMonoidal.ε i ≫ i.map (Functor.LaxMonoidal.ε F0)) ≫
      i.map (F0.map Representation.functionsOne)
  rw [i.map_comp, Category.assoc]

/-- The actual staged regular unit is split by the composite finite mean. -/
theorem stagedRegular_unit_augmentation :
    η[i.obj (regularAlgebra F0)] ≫ regularAugmentation (F0 ⋙ i) = 𝟙 _ := by
  rw [stagedRegular_unit]
  exact regular_one_augmentation (F0 ⋙ i)

/-- Free extension for the actual staged regular algebra is faithful. -/
def stagedRegularFreeFaithful :
    (InternalModule.freeFunctor (A := i.obj (regularAlgebra F0))).Faithful :=
  InternalModule.freeFunctorFaithfulOfSplitUnit (regularAugmentation (F0 ⋙ i))
    (stagedRegular_unit_augmentation F0 i)

/-- The averaging projector is the actual staged constant-function unit. -/
theorem stagedInvariant_factors_unit {X Y : N}
    (k : X ⟶ i.obj (regularAlgebra F0) ⊗ Y)
    (hk : ∀ g : G, k ≫ (i.map (regularTranslation F0 g) ▷ Y) = k) :
    k ≫ (regularAugmentation (F0 ⋙ i) ▷ Y) ≫
      (η[i.obj (regularAlgebra F0)] ▷ Y) = k := by
  rw [stagedRegular_unit]
  exact invariant_factors_unit (F0 ⋙ i) k hk

/-- Recover an actual ambient map from a genuinely invariant staged free
module map by the finite mean. -/
def stagedInvariantPreimage {X Y : N}
    (f : InternalModule.free (i.obj (regularAlgebra F0)) X ⟶
      InternalModule.free (i.obj (regularAlgebra F0)) Y) : X ⟶ Y :=
  RelativeTensor.freeUnit X ≫ f.hom ≫
    (regularAugmentation (F0 ⋙ i) ▷ Y) ≫ (λ_ Y).hom

include F0 i in
/-- Free generators of invariant module maps factor through the actual
staged regular unit. -/
theorem stagedInvariantPreimage_generator {X Y : N}
    (f : InternalModule.free (i.obj (regularAlgebra F0)) X ⟶
      InternalModule.free (i.obj (regularAlgebra F0)) Y)
    (hf : ∀ g : G, f.hom ≫ (i.map (regularTranslation F0 g) ▷ Y) =
      (i.map (regularTranslation F0 g) ▷ X) ≫ f.hom) :
    stagedInvariantPreimage F0 i f ≫ RelativeTensor.freeUnit Y =
      RelativeTensor.freeUnit X ≫ f.hom := by
  have hu (g : G) : RelativeTensor.freeUnit (A := i.obj (regularAlgebra F0)) X ≫
      (i.map (regularTranslation F0 g) ▷ X) = RelativeTensor.freeUnit X := by
    unfold RelativeTensor.freeUnit
    rw [Category.assoc, ← comp_whiskerRight, IsMonHom.one_hom]
  have h := stagedInvariant_factors_unit F0 i (RelativeTensor.freeUnit X ≫ f.hom)
    (fun g => by rw [Category.assoc, hf g, ← Category.assoc, hu g])
  simpa only [stagedInvariantPreimage, RelativeTensor.freeUnit, Category.assoc,
    Iso.hom_inv_id_assoc] using h

/-- Every genuinely invariant actual staged free-module map is the free
extension of the recovered actual ambient map. -/
theorem stagedFree_map_preimage {X Y : N}
    (f : InternalModule.free (i.obj (regularAlgebra F0)) X ⟶
      InternalModule.free (i.obj (regularAlgebra F0)) Y)
    (hf : ∀ g : G, f.hom ≫ (i.map (regularTranslation F0 g) ▷ Y) =
      (i.map (regularTranslation F0 g) ▷ X) ≫ f.hom) :
    InternalModule.freeMap (A := i.obj (regularAlgebra F0))
      (stagedInvariantPreimage F0 i f) = f := by
  apply RelativeTensor.free_hom_ext
  rw [RelativeTensor.freeUnit_naturality]
  exact stagedInvariantPreimage_generator F0 i f hf

/-- Invariance of an actual isomorphism implies invariance of its inverse. -/
theorem stagedFree_inverse_invariant {X Y : N}
    (e : InternalModule.free (i.obj (regularAlgebra F0)) X ≅
      InternalModule.free (i.obj (regularAlgebra F0)) Y)
    (he : ∀ g : G, e.hom.hom ≫ (i.map (regularTranslation F0 g) ▷ Y) =
      (i.map (regularTranslation F0 g) ▷ X) ≫ e.hom.hom) (g : G) :
    e.inv.hom ≫ (i.map (regularTranslation F0 g) ▷ X) =
      (i.map (regularTranslation F0 g) ▷ Y) ≫ e.inv.hom := by
  letI : IsIso e.hom.hom := (Mod_.forget (D := N) _).map_isIso e.hom
  apply (cancel_epi e.hom.hom).mp
  simp only [← Category.assoc]
  have hinv : e.hom.hom ≫ e.inv.hom = 𝟙 _ := congrArg Mod_.Hom.hom e.hom_inv_id
  rw [hinv, Category.id_comp, he g]
  simp only [Category.assoc, hinv]
  exact (Category.comp_id _).symm

/-- Genuine invariant actual free isomorphisms descend to actual ambient
isomorphisms, with no essential-image or comparison premise. -/
def stagedInvariantIso {X Y : N}
    (e : InternalModule.free (i.obj (regularAlgebra F0)) X ≅
      InternalModule.free (i.obj (regularAlgebra F0)) Y)
    (he : ∀ g : G, e.hom.hom ≫ (i.map (regularTranslation F0 g) ▷ Y) =
      (i.map (regularTranslation F0 g) ▷ X) ≫ e.hom.hom) : X ≅ Y := by
  letI := stagedRegularFreeFaithful F0 i
  refine { hom := stagedInvariantPreimage F0 i e.hom
           inv := stagedInvariantPreimage F0 i e.inv
           hom_inv_id := ?_
           inv_hom_id := ?_ }
  · apply (InternalModule.freeFunctor (A := i.obj (regularAlgebra F0))).map_injective
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
    change InternalModule.freeMap _ ≫ InternalModule.freeMap _ = _
    rw [stagedFree_map_preimage F0 i e.hom he,
      stagedFree_map_preimage F0 i e.inv (stagedFree_inverse_invariant F0 i e he)]
    exact e.hom_inv_id
  · apply (InternalModule.freeFunctor (A := i.obj (regularAlgebra F0))).map_injective
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
    change InternalModule.freeMap _ ≫ InternalModule.freeMap _ = _
    rw [stagedFree_map_preimage F0 i e.inv (stagedFree_inverse_invariant F0 i e he),
      stagedFree_map_preimage F0 i e.hom he]
    exact e.inv_hom_id

/-- The actual invariant lifting has precisely its original free image. -/
@[simp] theorem stagedInvariantIso_map_hom {X Y : N}
    (e : InternalModule.free (i.obj (regularAlgebra F0)) X ≅
      InternalModule.free (i.obj (regularAlgebra F0)) Y)
    (he : ∀ g : G, e.hom.hom ≫ (i.map (regularTranslation F0 g) ▷ Y) =
      (i.map (regularTranslation F0 g) ▷ X) ≫ e.hom.hom) :
    InternalModule.freeMap (A := i.obj (regularAlgebra F0))
      (stagedInvariantIso F0 i e he).hom = e.hom :=
  stagedFree_map_preimage F0 i e.hom he

end Paper18.Category.FixedBoundary
