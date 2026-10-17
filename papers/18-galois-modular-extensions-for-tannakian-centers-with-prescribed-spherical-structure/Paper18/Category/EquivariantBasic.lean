import Paper18.Category.Multiplicity
import Mathlib.CategoryTheory.Monoidal.Transport
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
import Mathlib.CategoryTheory.Preadditive.Transfer
import Mathlib.Algebra.Module.TransferInstance

/-!
# Equivariant objects for a weak categorical group action

The action has natural unit and multiplication isomorphisms, with triangle
and associativity coherence. No strictness of the action is assumed.
-/

noncomputable section
open Classical CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped BigOperators
universe v u w

namespace Paper18.Category

/-- A weak left action of a group on a category, with its actual coherence
isomorphisms. The order in `mulIso` is the usual left action order:
`ρ(g) (ρ(h) X) ≅ ρ(g h) X`. -/
structure WeakAction (G : Type w) [Group G] (C : Type u) [Category.{v} C] where
  ρ : G → C ⥤ C
  unitIso : ρ 1 ≅ 𝟭 C
  mulIso : ∀ g h, ρ h ⋙ ρ g ≅ ρ (g * h)
  assoc (g h k : G) (X : C) :
    (ρ g).map ((mulIso h k).hom.app X) ≫ (mulIso g (h * k)).hom.app X =
      (mulIso g h).hom.app ((ρ k).obj X) ≫ (mulIso (g * h) k).hom.app X ≫
        eqToHom (congrArg (fun t => (ρ t).obj X) (mul_assoc g h k))
  one_mul (g : G) (X : C) :
    (mulIso 1 g).hom.app X ≫
      eqToHom (congrArg (fun t => (ρ t).obj X) (one_mul g)) =
        unitIso.hom.app ((ρ g).obj X)
  mul_one (g : G) (X : C) :
    (mulIso g 1).hom.app X ≫
      eqToHom (congrArg (fun t => (ρ t).obj X) (mul_one g)) =
        (ρ g).map (unitIso.hom.app X)

namespace WeakAction
variable {G : Type w} [Group G] {C : Type u} [Category.{v} C] (A : WeakAction G C)

/-- Each translating functor is an autoequivalence. This is derived from
the inverse group element and the weak action isomorphisms. -/
instance rho_isEquivalence (g : G) : (A.ρ g).IsEquivalence := by
  let e : A.ρ g ⋙ A.ρ g⁻¹ ≅ 𝟭 C :=
    A.mulIso g⁻¹ g ≪≫ eqToIso (congrArg A.ρ (inv_mul_cancel g)) ≪≫ A.unitIso
  let f : A.ρ g⁻¹ ⋙ A.ρ g ≅ 𝟭 C :=
    A.mulIso g g⁻¹ ≪≫ eqToIso (congrArg A.ρ (mul_inv_cancel g)) ≪≫ A.unitIso
  exact Functor.IsEquivalence.mk' (A.ρ g⁻¹) e.symm f

/-- An object with coherent isomorphisms from all its translates. -/
structure Equivariant where
  obj : C
  structureIso : ∀ g : G, (A.ρ g).obj obj ≅ obj
  unit : (structureIso 1).hom = A.unitIso.hom.app obj
  mul (g h : G) :
    (A.ρ g).map ((structureIso h).hom) ≫ (structureIso g).hom =
      (A.mulIso g h).hom.app obj ≫ (structureIso (g * h)).hom

namespace Equivariant
variable {A}

/-- An equivariant morphism is an actual underlying morphism that commutes
with each equivariant structure isomorphism. -/
@[ext]
structure Hom (X Y : A.Equivariant) where
  hom : X.obj ⟶ Y.obj
  comm (g : G) : (A.ρ g).map hom ≫ (Y.structureIso g).hom =
    (X.structureIso g).hom ≫ hom

attribute [reassoc] Hom.comm

instance : Category A.Equivariant where
  Hom := Hom
  id X := ⟨𝟙 X.obj, by intro g; simp⟩
  comp f g := ⟨f.hom ≫ g.hom, by
    intro k
    simp only [Functor.map_comp, Category.assoc, Hom.comm]
    rw [← Category.assoc, Hom.comm, Category.assoc]⟩
  id_comp f := by ext; simp
  comp_id f := by ext; simp
  assoc f g h := by ext; simp [Category.assoc]

@[simp] theorem id_hom (X : A.Equivariant) : (𝟙 X : X ⟶ X).hom = 𝟙 X.obj := rfl
@[simp] theorem comp_hom {X Y Z : A.Equivariant} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

end Equivariant

/-- The actual forgetful functor from the equivariantization. -/
def forget : A.Equivariant ⥤ C where
  obj X := X.obj
  map f := f.hom

instance : A.forget.Faithful where
  map_injective h := Equivariant.Hom.ext h

section Linear
variable [Preadditive C] [Linear ℂ C]
  [∀ g : G, (A.ρ g).Additive] [∀ g : G, (A.ρ g).Linear ℂ]

namespace Equivariant

/-- Equivariant morphisms form the invariant subspace of the actual Hom
space. This supplies the additive and complex-linear structures. -/
def homSubmodule (X Y : A.Equivariant) : Submodule ℂ (X.obj ⟶ Y.obj) where
  carrier := {f | ∀ g, (A.ρ g).map f ≫ (Y.structureIso g).hom =
    (X.structureIso g).hom ≫ f}
  zero_mem' := by intro g; simp
  add_mem' := by intro f h hf hh g; simp [hf g, hh g]
  smul_mem' := by intro c f hf g; simp [hf g]

/-- Equivariant morphisms identified with a genuine linear subspace. -/
def homEquivSubmodule (X Y : A.Equivariant) :
    (X ⟶ Y) ≃ homSubmodule A X Y where
  toFun f := ⟨f.hom, f.comm⟩
  invFun f := ⟨f.val, f.property⟩
  left_inv f := by cases f; rfl
  right_inv f := by cases f; rfl

instance (X Y : A.Equivariant) : AddCommGroup (X ⟶ Y) :=
  (homEquivSubmodule A X Y).addCommGroup
instance (X Y : A.Equivariant) : Module ℂ (X ⟶ Y) :=
  Equiv.module ℂ (homEquivSubmodule A X Y)

@[simp] theorem zero_hom (X Y : A.Equivariant) : (0 : X ⟶ Y).hom = 0 := rfl
@[simp] theorem add_hom {X Y : A.Equivariant} (f h : X ⟶ Y) :
    (f + h).hom = f.hom + h.hom := rfl
@[simp] theorem smul_hom {X Y : A.Equivariant} (c : ℂ) (f : X ⟶ Y) :
    (c • f).hom = c • f.hom := rfl

instance : Preadditive A.Equivariant where
  add_comp := by intro X Y Z f g h; apply Hom.ext; simp [Preadditive.add_comp]
  comp_add := by intro X Y Z f g h; apply Hom.ext; simp [Preadditive.comp_add]

instance : CategoryTheory.Linear ℂ A.Equivariant where
  smul_comp := by intro X Y Z c f g; apply Hom.ext; simp
  comp_smul := by intro X Y Z f c g; apply Hom.ext; simp

/-- The equivariant Hom subspace identification as a linear equivalence. -/
def homLinearEquivSubmodule (X Y : A.Equivariant) :
    (X ⟶ Y) ≃ₗ[ℂ] homSubmodule A X Y where
  toEquiv := homEquivSubmodule A X Y
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] (X Y : A.Equivariant) :
    FiniteDimensional ℂ (X ⟶ Y) :=
  (homLinearEquivSubmodule A X Y).symm.finiteDimensional

end Equivariant

instance : A.forget.Additive where
  map_add := by intros; rfl
instance : A.forget.Linear ℂ where
  map_smul _ _ := rfl

end Linear
end WeakAction
end Paper18.Category
