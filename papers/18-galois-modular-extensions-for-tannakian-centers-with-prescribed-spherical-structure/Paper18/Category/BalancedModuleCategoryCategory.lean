import Paper18.Category.BalancedModuleCategoryExternalBalanced
import Paper18.Category.BalancedModuleCategoryComparison

/-! # The category of actual balanced functors and actual restriction -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits
open MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u vE uE
namespace Paper18.Category.BalancedModuleCategory
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  {A B : D} [MonObj A] [MonObj B]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
variable {E : Type uE} [Category.{vE} E]
namespace BalancedFunctor

/-- Actual natural transformations commuting with the actual balancing. -/
structure Hom (F G : BalancedFunctor (A := A) (B := B) E) where
  hom : F.toFunctor ⟶ G.toFunctor
  balanced : ∀ (M : Mod_ D A) (X : D) (N : RightModules B),
    F.comparison.hom.app ((M, X), N) ≫ hom.app (M, rightAmbientTensor N X) =
      hom.app (RelativeTensor.ambientTensor M X, N) ≫ G.comparison.hom.app ((M, X), N)

@[ext] theorem Hom.ext {F G : BalancedFunctor (A := A) (B := B) E}
    {f g : Hom F G} (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance : Category (BalancedFunctor (A := A) (B := B) E) where
  Hom := Hom
  id F := ⟨𝟙 F.toFunctor, by
    intro M X N
    change F.comparison.hom.app ((M, X), N) ≫ 𝟙 _ = 𝟙 _ ≫ F.comparison.hom.app ((M, X), N)
    exact (Category.comp_id _).trans (Category.id_comp _).symm⟩
  comp f g := ⟨f.hom ≫ g.hom, by
    intro M X N
    change _ ≫ (f.hom.app (M, rightAmbientTensor N X) ≫ g.hom.app (M, rightAmbientTensor N X)) =
      (f.hom.app (RelativeTensor.ambientTensor M X, N) ≫ g.hom.app (RelativeTensor.ambientTensor M X, N)) ≫ _
    exact vertical_square (f.balanced M X N) (g.balanced M X N)⟩
  id_comp f := Hom.ext (Category.id_comp f.hom)
  comp_id f := Hom.ext (Category.comp_id f.hom)
  assoc f g h := Hom.ext (Category.assoc f.hom g.hom h.hom)

/-- An actual balanced natural isomorphism determines an actual
isomorphism in the category of balanced functors. -/
def isoMk {F G : BalancedFunctor (A := A) (B := B) E} (e : F.toFunctor ≅ G.toFunctor)
    (h : ∀ (M : Mod_ D A) (X : D) (N : RightModules B),
      F.comparison.hom.app ((M, X), N) ≫ e.hom.app (M, rightAmbientTensor N X) =
        e.hom.app (RelativeTensor.ambientTensor M X, N) ≫ G.comparison.hom.app ((M, X), N)) : F ≅ G where
  hom := ⟨e.hom, h⟩
  inv := ⟨e.inv, by
    intro M X N
    apply (cancel_epi (e.app (RelativeTensor.ambientTensor M X, N)).hom).mp
    change (e.app (RelativeTensor.ambientTensor M X, N)).hom ≫
        (G.comparison.hom.app ((M, X), N) ≫ (e.app (M, rightAmbientTensor N X)).inv) =
      (e.app (RelativeTensor.ambientTensor M X, N)).hom ≫
        ((e.app (RelativeTensor.ambientTensor M X, N)).inv ≫ F.comparison.hom.app ((M, X), N))
    have hh := h M X N
    change _ ≫ (e.app (M, rightAmbientTensor N X)).hom =
      (e.app (RelativeTensor.ambientTensor M X, N)).hom ≫ _ at hh
    rw [← Category.assoc, ← hh, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Iso.hom_inv_id_assoc]⟩
  hom_inv_id := Hom.ext e.hom_inv_id
  inv_hom_id := Hom.ext e.inv_hom_id

end BalancedFunctor

/-- Restriction along the actual external balanced tensor. -/
def restriction : (BimoduleRelativeTensor.Native A B ⥤ E) ⥤ BalancedFunctor (A := A) (B := B) E where
  obj K := (nativeBalanced (A := A) (B := B)).postcompose K
  map τ := ⟨Functor.whiskerLeft external τ, by
    intro M X N
    exact τ.naturality (balancingIso M X N).hom⟩
  map_id K := by apply BalancedFunctor.Hom.ext; rfl
  map_comp τ σ := by apply BalancedFunctor.Hom.ext; rfl

variable [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]

/-- Every actual balanced comparison map extends uniquely. -/
def restrictionFullyFaithful (SA : SeparableAlgebra A) (SB : SeparableAlgebra B) :
    restriction (A := A) (B := B) (E := E) |>.FullyFaithful where
  preimage τ := extendBalancedNatTrans SA SB τ.hom τ.balanced
  map_preimage τ := by
    apply BalancedFunctor.Hom.ext
    apply NatTrans.ext
    funext X
    exact extendBalancedNatTrans_external τ.hom SA SB τ.balanced X.1 X.2
  preimage_map τ := by
    apply natTrans_ext SA SB
    intro M N
    exact extendBalancedNatTrans_external
      (Functor.whiskerLeft external τ) SA SB (fun M X N => τ.naturality (balancingIso M X N).hom) M N

/-- The coequalizer construction gives every actual balanced functor
as a value of restriction, up to an actual balanced isomorphism. -/
def restrictionObjIso [HasCoequalizers E] (SB : SeparableAlgebra B)
    (F : BalancedFunctor (A := A) (B := B) E) :
    restriction.obj F.extension ≅ F :=
  BalancedFunctor.isoMk (F.extensionExternalNatIso SB) (F.extensionExternalNatIso_balanced SB)

end Paper18.Category.BalancedModuleCategory
