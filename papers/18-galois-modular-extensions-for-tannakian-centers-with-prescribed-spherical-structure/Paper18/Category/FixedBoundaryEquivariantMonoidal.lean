import Paper18.Category.FixedBoundaryEquivariantTransport
import Paper18.Category.FixedBoundaryActionMonoidal
import Paper18.Category.EquivariantMonoidal

/-! # Strong tensor transport of actual equivariant objects -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal
universe v u v' u' w
namespace Paper18.Category.WeakAction.Intertwiner
variable {G : Type w} [Group G]
  {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  {A : WeakAction G C} {B : WeakAction G D}
  [∀ g, (A.ρ g).Monoidal] [∀ g, (B.ρ g).Monoidal]
  [A.IsMonoidal] [B.IsMonoidal]
  (F : A.Intertwiner B) [F.functor.Monoidal] [F.IsMonoidal]

/-- The original unit comparison is an actual equivariant isomorphism. -/
def equivariantUnitIso : 𝟙_ B.Equivariant ≅ F.equivariantFunctor.obj (𝟙_ A.Equivariant) :=
  Equivariant.mkIso B (εIso F.functor) (by
    intro g
    change (B.ρ g).map (ε F.functor) ≫ (F.comparison g).inv.app (𝟙_ C) ≫
        F.functor.map (η (A.ρ g)) = η (B.ρ g) ≫ ε F.functor
    apply (cancel_epi (ε (B.ρ g))).mp
    have hc := NatTrans.IsMonoidal.unit (τ := (F.comparison g).inv)
    simp only [Functor.LaxMonoidal.comp_ε, Category.assoc] at hc
    slice_lhs 1 3 => rw [hc]
    simp [Category.assoc, ← F.functor.map_comp])

/-- The original tensor comparison respects the actual transported
structure maps on equivariant objects. -/
def equivariantTensorIso (X Y : A.Equivariant) :
    F.equivariantFunctor.obj X ⊗ F.equivariantFunctor.obj Y ≅
      F.equivariantFunctor.obj (X ⊗ Y) :=
  Equivariant.mkIso B (μIso F.functor X.obj Y.obj) (by
    intro g
    change (B.ρ g).map (μ F.functor X.obj Y.obj) ≫
        (F.comparison g).inv.app (X.obj ⊗ Y.obj) ≫
        F.functor.map (δ (A.ρ g) X.obj Y.obj ≫
          ((X.structureIso g).hom ⊗ₘ (Y.structureIso g).hom)) =
      (δ (B.ρ g) (F.functor.obj X.obj) (F.functor.obj Y.obj) ≫
        (((F.comparison g).inv.app X.obj ≫ F.functor.map (X.structureIso g).hom) ⊗ₘ
          ((F.comparison g).inv.app Y.obj ≫ F.functor.map (Y.structureIso g).hom))) ≫
        μ F.functor X.obj Y.obj
    apply (cancel_epi (μ (B.ρ g) (F.functor.obj X.obj) (F.functor.obj Y.obj))).mp
    simp only [Category.assoc]
    have hc := NatTrans.IsMonoidal.tensor (τ := (F.comparison g).inv) X.obj Y.obj
    simp only [Functor.LaxMonoidal.comp_μ, Category.assoc] at hc
    slice_lhs 1 3 => rw [hc]
    simp only [Category.assoc, ← F.functor.map_comp, Functor.Monoidal.μ_δ_assoc]
    rw [← Functor.LaxMonoidal.μ_natural, tensorHom_comp_tensorHom_assoc])

/-- Coherences lift from the actual ambient tensor functor under the
faithful equivariant forgetful functor. -/
def equivariantFunctorCoreMonoidal : F.equivariantFunctor.CoreMonoidal where
  εIso := F.equivariantUnitIso
  μIso := F.equivariantTensorIso
  μIso_hom_natural_left {X Y} f Z := by
    apply Equivariant.Hom.ext
    change (F.functor.map f.hom ⊗ₘ 𝟙 (F.functor.obj Z.obj)) ≫ μ F.functor Y.obj Z.obj =
      μ F.functor X.obj Z.obj ≫ F.functor.map (f.hom ⊗ₘ 𝟙 Z.obj)
    rw [MonoidalCategory.tensorHom_id, MonoidalCategory.tensorHom_id]
    exact Functor.LaxMonoidal.μ_natural_left F.functor f.hom Z.obj
  μIso_hom_natural_right {X Y} Z f := by
    apply Equivariant.Hom.ext
    change (𝟙 (F.functor.obj Z.obj) ⊗ₘ F.functor.map f.hom) ≫ μ F.functor Z.obj Y.obj =
      μ F.functor Z.obj X.obj ≫ F.functor.map (𝟙 Z.obj ⊗ₘ f.hom)
    rw [MonoidalCategory.id_tensorHom, MonoidalCategory.id_tensorHom]
    exact Functor.LaxMonoidal.μ_natural_right F.functor Z.obj f.hom
  associativity X Y Z := by
    apply Equivariant.Hom.ext
    change (μ F.functor X.obj Y.obj ⊗ₘ 𝟙 (F.functor.obj Z.obj)) ≫
        μ F.functor (X.obj ⊗ Y.obj) Z.obj ≫ F.functor.map (α_ X.obj Y.obj Z.obj).hom =
      (α_ (F.functor.obj X.obj) (F.functor.obj Y.obj) (F.functor.obj Z.obj)).hom ≫
        (𝟙 (F.functor.obj X.obj) ⊗ₘ μ F.functor Y.obj Z.obj) ≫
        μ F.functor X.obj (Y.obj ⊗ Z.obj)
    rw [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom]
    exact Functor.LaxMonoidal.associativity F.functor X.obj Y.obj Z.obj
  left_unitality X := by
    apply Equivariant.Hom.ext
    change (λ_ (F.functor.obj X.obj)).hom =
      (ε F.functor ⊗ₘ 𝟙 (F.functor.obj X.obj)) ≫ μ F.functor (𝟙_ C) X.obj ≫
        F.functor.map (λ_ X.obj).hom
    rw [MonoidalCategory.tensorHom_id]
    exact Functor.LaxMonoidal.left_unitality F.functor X.obj
  right_unitality X := by
    apply Equivariant.Hom.ext
    change (ρ_ (F.functor.obj X.obj)).hom =
      (𝟙 (F.functor.obj X.obj) ⊗ₘ ε F.functor) ≫ μ F.functor X.obj (𝟙_ C) ≫
        F.functor.map (ρ_ X.obj).hom
    rw [MonoidalCategory.id_tensorHom]
    exact Functor.LaxMonoidal.right_unitality F.functor X.obj

/-- A genuine monoidal action intertwiner induces a genuine strong tensor
functor between the actual equivariantizations. -/
instance equivariantFunctorMonoidal : F.equivariantFunctor.Monoidal :=
  F.equivariantFunctorCoreMonoidal.toMonoidal


variable {F} {H : A.Intertwiner B} [H.functor.Monoidal] [H.IsMonoidal]

/-- A monoidal action-compatible transformation remains monoidal after
passing to the actual equivariantizations. -/
instance Transformation.equivariantNatTransMonoidal (τ : Transformation F H)
    [NatTrans.IsMonoidal τ.natTrans] : NatTrans.IsMonoidal τ.equivariantNatTrans where
  unit := by
    apply Equivariant.Hom.ext
    change ε F.functor ≫ τ.natTrans.app (𝟙_ C) = ε H.functor
    exact NatTrans.IsMonoidal.unit (τ := τ.natTrans)
  tensor X Y := by
    apply Equivariant.Hom.ext
    change μ F.functor X.obj Y.obj ≫ τ.natTrans.app (X.obj ⊗ Y.obj) =
      (τ.natTrans.app X.obj ⊗ₘ τ.natTrans.app Y.obj) ≫ μ H.functor X.obj Y.obj
    exact NatTrans.IsMonoidal.tensor (τ := τ.natTrans) X.obj Y.obj

end Paper18.Category.WeakAction.Intertwiner
