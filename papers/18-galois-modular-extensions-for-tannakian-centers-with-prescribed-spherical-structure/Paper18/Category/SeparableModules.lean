import Mathlib.CategoryTheory.Monoidal.Mod_
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
# Separable internal algebras and actual module sections

Separability consists of an actual bimodule section of multiplication.
The averaging maps below are constructed from that section and the actual
module actions.
-/

noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped MonObj
universe v u
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- An actual bimodule section of internal multiplication. -/
structure SeparableAlgebra (A : C) [MonObj A] where
  section_ : A ⟶ A ⊗ A
  section_mul : section_ ≫ μ[A] = 𝟙 A
  left_linear : μ[A] ≫ section_ =
    (A ◁ section_) ≫ (α_ A A A).inv ≫ (μ[A] ▷ A)
  right_linear : μ[A] ≫ section_ =
    (section_ ▷ A) ≫ (α_ A A A).hom ≫ (A ◁ μ[A])

namespace SeparableAlgebra
variable {A : C} [MonObj A] (S : SeparableAlgebra A)

/-- The actual separability element. -/
def element : 𝟙_ C ⟶ A ⊗ A := η[A] ≫ S.section_

@[reassoc (attr := simp)]
theorem element_mul : S.element ≫ μ[A] = η[A] := by
  simp [element, S.section_mul]

/-- Multiplication on the right leg of the separability element recovers
the bimodule section. -/
theorem element_right :
    (λ_ A).inv ≫ S.element ▷ A ≫ (α_ A A A).hom ≫ (A ◁ μ[A]) = S.section_ := by
  unfold element
  rw [comp_whiskerRight, Category.assoc, ← S.right_linear]
  simp

/-- Multiplication on the left leg of the separability element recovers
the same bimodule section. -/
theorem element_left :
    (ρ_ A).inv ≫ (A ◁ S.element) ≫ (α_ A A A).inv ≫ (μ[A] ▷ A) = S.section_ := by
  unfold element
  rw [whiskerLeft_comp, Category.assoc, ← S.left_linear]
  simp

end SeparableAlgebra

namespace InternalModule
variable (A : C) [MonObj A]

/-- The actual free internal module on an ambient object. -/
def free (X : C) : Mod_ C A :=
  letI : ModObj A (A ⊗ X) :=
    { smul := (α_ A A X).inv ≫ μ[A] ▷ X
      one_smul' := by
        change η[A] ▷ (A ⊗ X) ≫ (α_ A A X).inv ≫ μ[A] ▷ X = (λ_ (A ⊗ X)).hom
        calc
          _ = (α_ (𝟙_ C) A X).inv ≫ (η[A] ▷ A ≫ μ[A]) ▷ X := by monoidal
          _ = _ := by rw [MonObj.one_mul]; monoidal
      mul_smul' := by
        change μ[A] ▷ (A ⊗ X) ≫ (α_ A A X).inv ≫ μ[A] ▷ X =
          (α_ A A (A ⊗ X)).hom ≫ (A ◁ ((α_ A A X).inv ≫ μ[A] ▷ X)) ≫
            (α_ A A X).inv ≫ μ[A] ▷ X
        calc
          _ = (α_ (A ⊗ A) A X).inv ≫ (μ[A] ▷ A ≫ μ[A]) ▷ X := by monoidal
          _ = (α_ (A ⊗ A) A X).inv ≫
              ((α_ A A A).hom ≫ (A ◁ μ[A]) ≫ μ[A]) ▷ X := by rw [MonObj.mul_assoc]
          _ = _ := by monoidal }
  ⟨A ⊗ X⟩

@[simp] theorem free_X (X : C) : (free A X).X = A ⊗ X := rfl

@[simp] theorem free_smul (X : C) :
    γ[A,(free A X).X] = (α_ A A X).inv ≫ μ[A] ▷ X := rfl

variable {A}

/-- Explicit form of module associativity for the self-action. -/
@[reassoc]
theorem mul_smul (M : Mod_ C A) :
    μ[A] ▷ M.X ≫ γ[A,M.X] = (α_ A A M.X).hom ≫ (A ◁ γ[A,M.X]) ≫ γ[A,M.X] :=
  ModObj.mul_smul (M := A) M.X

/-- Explicit form of module unitality for the self-action. -/
@[reassoc (attr := simp)]
theorem one_smul (M : Mod_ C A) : η[A] ▷ M.X ≫ γ[A,M.X] = (λ_ M.X).hom :=
  ModObj.one_smul (M := A) M.X


/-- The module forgetful functor is faithful on actual underlying morphisms. -/
instance forget_faithful : (Mod_.forget (D := C) A).Faithful where
  map_injective h := Mod_.Hom.ext h

/-- The actual module morphism induced by the action itself. -/
def actionHom (M : Mod_ C A) : free A M.X ⟶ M :=
  Mod_.Hom.mk' γ[A,M.X] (by
    change ((α_ A A M.X).inv ≫ μ[A] ▷ M.X) ≫ γ[A,M.X] =
      (A ◁ γ[A,M.X]) ≫ γ[A,M.X]
    rw [Category.assoc, mul_smul]
    simp)

/-- Tensoring a map with the algebra gives an actual map of free modules. -/
def freeMap {X Y : C} (f : X ⟶ Y) : free A X ⟶ free A Y :=
  Mod_.Hom.mk' (A ◁ f) (by
    change ((α_ A A X).inv ≫ μ[A] ▷ X) ≫ (A ◁ f) =
      (A ◁ A ◁ f) ≫ (α_ A A Y).inv ≫ μ[A] ▷ Y
    rw [Category.assoc, associator_inv_naturality_right_assoc, whisker_exchange])

/-- The universal free-module lift of an ambient morphism. -/
def freeLift {M : Mod_ C A} {X : C} (f : X ⟶ M.X) : free A X ⟶ M :=
  freeMap f ≫ actionHom M

@[simp] theorem freeLift_hom {M : Mod_ C A} {X : C} (f : X ⟶ M.X) :
    (freeLift f).hom = (A ◁ f) ≫ γ[A,M.X] := rfl

/-- Evaluation on the unit recovers the original ambient map. -/
@[simp]
theorem unit_freeLift {M : Mod_ C A} {X : C} (f : X ⟶ M.X) :
    (λ_ X).inv ≫ η[A] ▷ X ≫ (freeLift f).hom = f := by
  rw [freeLift_hom]
  rw [← whisker_exchange_assoc, ← leftUnitor_inv_naturality_assoc, one_smul]
  simp

/-- The universal free lift is natural in its module target. -/
@[reassoc]
theorem freeLift_comp {M N : Mod_ C A} {X : C} (g : X ⟶ M.X) (f : M ⟶ N) :
    freeLift g ≫ f = freeLift (g ≫ f.hom) := by
  apply Mod_.Hom.ext
  change ((A ◁ g) ≫ γ[A,M.X]) ≫ f.hom = (A ◁ (g ≫ f.hom)) ≫ γ[A,N.X]
  have hf : γ[A,M.X] ≫ f.hom = (A ◁ f.hom) ≫ γ[A,N.X] :=
    IsMod_Hom.smul_hom (A := A) (f := f.hom)
  rw [Category.assoc, hf, whiskerLeft_comp, Category.assoc]

/-- Free modules detect monomorphisms in the underlying category. -/
instance forget_preservesMonomorphisms : (Mod_.forget (D := C) A).PreservesMonomorphisms where
  preserves {M N} f _ := by
    constructor
    intro X g h eq
    change g ≫ f.hom = h ≫ f.hom at eq
    have hh : freeLift g = freeLift h := by
      apply (cancel_mono f).mp
      rw [freeLift_comp, freeLift_comp, eq]
    have hu := congrArg (fun k : free A X ⟶ M =>
      (λ_ X).inv ≫ η[A] ▷ X ≫ k.hom) hh
    simpa only [unit_freeLift] using hu

end InternalModule

namespace SeparableAlgebra
variable {A : C} [MonObj A] (S : SeparableAlgebra A)

/-- The actual section of a module action induced by the algebra's
bimodule section. -/
def moduleSection (M : Mod_ C A) : M.X ⟶ A ⊗ M.X :=
  (λ_ M.X).inv ≫ S.element ▷ M.X ≫ (α_ A A M.X).hom ≫ (A ◁ γ[A,M.X])

@[reassoc (attr := simp)]
theorem moduleSection_action (M : Mod_ C A) :
    S.moduleSection M ≫ γ[A,M.X] = 𝟙 M.X := by
  unfold moduleSection
  simp only [Category.assoc]
  rw [← InternalModule.mul_smul, ← comp_whiskerRight_assoc, S.element_mul]
  simp

/-- Naturality of the induced section with respect to module morphisms. -/
@[reassoc]
theorem moduleSection_naturality {M N : Mod_ C A} (f : M ⟶ N) :
    f.hom ≫ S.moduleSection N = S.moduleSection M ≫ (A ◁ f.hom) := by
  have hf : γ[A,M.X] ≫ f.hom = (A ◁ f.hom) ≫ γ[A,N.X] :=
    IsMod_Hom.smul_hom (A := A) (f := f.hom)
  unfold moduleSection
  simp only [Category.assoc]
  rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc,
    associator_naturality_right_assoc, ← whiskerLeft_comp, ← hf,
    whiskerLeft_comp]


/-- The section intertwines the original module action with the algebra
bimodule section. -/
theorem action_moduleSection (M : Mod_ C A) :
    γ[A,M.X] ≫ S.moduleSection M =
      S.section_ ▷ M.X ≫ (α_ A A M.X).hom ≫ (A ◁ γ[A,M.X]) := by
  have hassoc : (A ◁ γ[A,M.X]) ≫ γ[A,M.X] =
      (α_ A A M.X).inv ≫ μ[A] ▷ M.X ≫ γ[A,M.X] := by
    rw [InternalModule.mul_smul]
    simp
  calc
    _ = (λ_ (A ⊗ M.X)).inv ≫ S.element ▷ (A ⊗ M.X) ≫
        (α_ A A (A ⊗ M.X)).hom ≫ (A ◁ ((A ◁ γ[A,M.X]) ≫ γ[A,M.X])) := by
      unfold moduleSection
      rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc,
        associator_naturality_right_assoc, ← whiskerLeft_comp]
      rfl
    _ = ((λ_ A).inv ≫ S.element ▷ A ≫ (α_ A A A).hom ≫ (A ◁ μ[A])) ▷ M.X ≫
        (α_ A A M.X).hom ≫ (A ◁ γ[A,M.X]) := by
      rw [hassoc]
      monoidal
    _ = _ := by rw [S.element_right]

/-- The same section intertwines the free-module action. -/
theorem free_action_moduleSection (M : Mod_ C A) :
    (A ◁ S.moduleSection M) ≫ γ[A,(InternalModule.free A M.X).X] =
      S.section_ ▷ M.X ≫ (α_ A A M.X).hom ≫ (A ◁ γ[A,M.X]) := by
  rw [InternalModule.free_smul]
  unfold moduleSection
  simp only [whiskerLeft_comp, Category.assoc]
  rw [associator_inv_naturality_right_assoc, whisker_exchange]
  calc
    _ = ((ρ_ A).inv ≫ (A ◁ S.element) ≫ (α_ A A A).inv ≫ (μ[A] ▷ A)) ▷ M.X ≫
        (α_ A A M.X).hom ≫ (A ◁ γ[A,M.X]) := by monoidal
    _ = _ := by rw [S.element_left]

/-- The induced section is an actual morphism of internal modules. -/
instance moduleSection_isModHom (M : Mod_ C A) :
    IsMod_Hom A (M := M.X) (N := (InternalModule.free A M.X).X) (S.moduleSection M) where
  smul_hom := by
    change γ[A,M.X] ≫ S.moduleSection M =
      (A ◁ S.moduleSection M) ≫ γ[A,(InternalModule.free A M.X).X]
    rw [S.action_moduleSection, S.free_action_moduleSection]


/-- The induced section bundled as an actual module morphism. -/
def moduleSectionHom (M : Mod_ C A) : M ⟶ InternalModule.free A M.X :=
  ⟨S.moduleSection M⟩

/-- Averaging an arbitrary underlying map gives an actual module morphism. -/
def average {M N : Mod_ C A} (f : M.X ⟶ N.X) : M ⟶ N :=
  S.moduleSectionHom M ≫ InternalModule.freeLift f

@[simp] theorem average_hom {M N : Mod_ C A} (f : M.X ⟶ N.X) :
    (S.average f).hom = S.moduleSection M ≫ (A ◁ f) ≫ γ[A,N.X] := rfl

/-- Averaging fixes every actual module morphism. -/
@[simp]
theorem average_moduleHom {M N : Mod_ C A} (f : M ⟶ N) : S.average f.hom = f := by
  apply Mod_.Hom.ext
  rw [average_hom, ← S.moduleSection_naturality_assoc, S.moduleSection_action]
  simp

/-- Averaging commutes with precomposition by a module map. -/
@[reassoc]
theorem comp_average {M N O : Mod_ C A} (f : M ⟶ N) (g : N.X ⟶ O.X) :
    f ≫ S.average g = S.average (f.hom ≫ g) := by
  apply Mod_.Hom.ext
  change f.hom ≫ (S.moduleSection N ≫ (A ◁ g) ≫ γ[A,O.X]) =
    S.moduleSection M ≫ (A ◁ (f.hom ≫ g)) ≫ γ[A,O.X]
  rw [S.moduleSection_naturality_assoc, whiskerLeft_comp]
  simp only [Category.assoc]

/-- Averaging commutes with postcomposition by a module map. -/
@[reassoc]
theorem average_comp {M N O : Mod_ C A} (f : M.X ⟶ N.X) (g : N ⟶ O) :
    S.average f ≫ g = S.average (f ≫ g.hom) := by
  unfold average
  rw [Category.assoc, InternalModule.freeLift_comp]

end SeparableAlgebra
end Paper18.Category
