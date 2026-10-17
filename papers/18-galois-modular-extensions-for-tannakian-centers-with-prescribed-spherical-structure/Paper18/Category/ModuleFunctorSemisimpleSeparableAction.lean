import Paper18.Category.TannakianDeequivariantization
import Mathlib.CategoryTheory.Monoidal.Action.End

/-! # Actual separable averaging for arbitrary native actions

Transporting the actual bimodule section to the composition monoidal
category and evaluating its identities gives separable averaging in an
arbitrary category on which the algebra acts. No pivotal data enter.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u v' u'
namespace Paper18.Category.ModuleFunctor.SeparableAction
open MonoidalLeftAction
attribute [local instance] endofunctorMonoidalCategory
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {M : Type u'} [Category.{v'} M] [MonoidalLeftAction C M]
  {A : C} [MonObj A]

/-- The actual algebra of endofunctors supplied by the native action. -/
abbrev actionAlgebra : (M ⥤ M)ᴹᵒᵖ := (curriedActionMop C M).obj A

instance actionAlgebra_monObj : MonObj (actionAlgebra (M := M) (A := A)) :=
  Functor.monObjObj (F := curriedActionMop C M) A

/-- Evaluation takes an internal module for the actual action algebra to
an actual module in the category being acted upon. -/
def evaluate (m : M) (B : Mod_ ((M ⥤ M)ᴹᵒᵖ) (actionAlgebra (M := M) (A := A))) :
    Mod_ M A := by
  letI : ModObj A (B.X.unmop.obj m) :=
    { smul := γ[actionAlgebra (M := M) (A := A),B.X].unmop.app m
      one_smul' := by
        have h := congrArg (fun f => f.unmop.app m)
          (ModObj.one_smul (M := actionAlgebra (M := M) (A := A)) B.X)
        change ((λₗ[C] (B.X.unmop.obj m)).inv ≫ η[A] ⊵ₗ (B.X.unmop.obj m)) ≫
          γ[actionAlgebra (M := M) (A := A),B.X].unmop.app m = 𝟙 _ at h
        apply (cancel_epi (λₗ[C] (B.X.unmop.obj m)).inv).mp
        simpa only [assoc, Iso.inv_hom_id] using h
      mul_smul' := by
        have h := congrArg (fun f => f.unmop.app m)
          (ModObj.mul_smul (M := actionAlgebra (M := M) (A := A)) B.X)
        change ((αₗ A A (B.X.unmop.obj m)).inv ≫ μ[A] ⊵ₗ (B.X.unmop.obj m)) ≫
          γ[actionAlgebra (M := M) (A := A),B.X].unmop.app m =
            𝟙 _ ≫ A ⊴ₗ γ[actionAlgebra (M := M) (A := A),B.X].unmop.app m ≫
              γ[actionAlgebra (M := M) (A := A),B.X].unmop.app m at h
        apply (cancel_epi (αₗ A A (B.X.unmop.obj m)).inv).mp
        simpa only [assoc, Iso.inv_hom_id_assoc, id_comp] using h }
  exact ⟨B.X.unmop.obj m⟩

@[simp] lemma evaluate_X (m : M)
    (B : Mod_ ((M ⥤ M)ᴹᵒᵖ) (actionAlgebra (M := M) (A := A))) :
    (evaluate m B).X = B.X.unmop.obj m := rfl

/-- The evaluated actual module morphism. -/
def evaluateMap (m : M)
    {B D : Mod_ ((M ⥤ M)ᴹᵒᵖ) (actionAlgebra (M := M) (A := A))} (f : B ⟶ D) :
    evaluate m B ⟶ evaluate m D :=
  Mod_.Hom.mk' (f.hom.unmop.app m) (by
    exact congrArg (fun a => a.unmop.app m) (IsMod_Hom.smul_hom (A := actionAlgebra (M := M) (A := A)) (f := f.hom)))

/-- An external module becomes the constant internal module for the
actual action algebra. -/
def constant (X : Mod_ M A) :
    Mod_ ((M ⥤ M)ᴹᵒᵖ) (actionAlgebra (M := M) (A := A)) := by
  let B : (M ⥤ M)ᴹᵒᵖ := mop ((Functor.const M).obj X.X)
  letI : ModObj (actionAlgebra (M := M) (A := A)) B :=
    { smul := Quiver.Hom.mop
        { app := fun _ => γ[A,X.X]
          naturality := by
            intro m n f
            change (A ⊴ₗ 𝟙 X.X) ≫ γ[A,X.X] = γ[A,X.X] ≫ 𝟙 X.X
            simp }
      one_smul' := by
        apply Quiver.Hom.unmop_inj
        ext m
        change ((λₗ[C] X.X).inv ≫ η[A] ⊵ₗ X.X) ≫ γ[A,X.X] = 𝟙 _
        rw [assoc, ModObj.one_smul, Iso.inv_hom_id]
      mul_smul' := by
        apply Quiver.Hom.unmop_inj
        ext m
        change ((αₗ A A X.X).inv ≫ μ[A] ⊵ₗ X.X) ≫ γ[A,X.X] =
          𝟙 _ ≫ (A ⊴ₗ γ[A,X.X]) ≫ γ[A,X.X]
        rw [assoc, ModObj.mul_smul, Iso.inv_hom_id_assoc, id_comp] }
  exact ⟨B⟩

/-- The actual constant map of internal modules. -/
def constantMap {X Y : Mod_ M A} (f : X ⟶ Y) : constant X ⟶ constant Y :=
  Mod_.Hom.mk' (Quiver.Hom.mop
    { app := fun _ => f.hom
      naturality := by intro m n g; simp }) (by
      apply Quiver.Hom.unmop_inj
      ext m
      exact IsMod_Hom.smul_hom (f := f.hom))

variable (S : SeparableAlgebra A)

/-- Separability transported through the actual strong monoidal action. -/
def actionSeparable : SeparableAlgebra (actionAlgebra (M := M) (A := A)) :=
  S.map (curriedActionMop C M)

/-- An arbitrary external map is averaged by the actual algebra section. -/
def average {X Y : Mod_ M A} (f : X.X ⟶ Y.X) : X ⟶ Y :=
  Mod_.Hom.mk' (((actionSeparable (M := M) S).average
    (M := constant X) (N := constant Y) (Quiver.Hom.mop
      { app := fun _ => f
        naturality := by intro m n g; simp })).hom.unmop.app X.X) (by
    exact congrArg (fun a => a.unmop.app X.X)
      (IsMod_Hom.smul_hom (A := actionAlgebra (M := M) (A := A)) (f := ((actionSeparable (M := M) S).average
        (M := constant X) (N := constant Y) (Quiver.Hom.mop
          { app := fun _ => f
            naturality := by intro m n g; simp })).hom)))

/-- The actual separability section on an external module. -/
def section_ (X : Mod_ M A) : X.X ⟶ A ⊙ₗ X.X :=
  ((actionSeparable (M := M) S).moduleSection (constant X)).unmop.app X.X

@[simp] lemma average_hom {X Y : Mod_ M A} (f : X.X ⟶ Y.X) :
    (average S f).hom = section_ S X ≫ (A ⊴ₗ f) ≫ γ[A,Y.X] := rfl

@[reassoc (attr := simp)]
lemma section_action (X : Mod_ M A) : section_ S X ≫ γ[A,X.X] = 𝟙 X.X :=
  congrArg (fun a => a.unmop.app X.X)
    ((actionSeparable (M := M) S).moduleSection_action (constant X))

@[simp] lemma average_moduleHom {X Y : Mod_ M A} (f : X ⟶ Y) : average S f.hom = f := by
  apply Mod_.Hom.ext
  exact congrArg (fun a => a.hom.unmop.app X.X)
    ((actionSeparable (M := M) S).average_moduleHom (constantMap f))

@[reassoc]
lemma section_naturality {X Y : Mod_ M A} (f : X ⟶ Y) :
    f.hom ≫ section_ S Y = section_ S X ≫ (A ⊴ₗ f.hom) :=
  congrArg (fun a => a.unmop.app X.X)
    ((actionSeparable (M := M) S).moduleSection_naturality (constantMap f))

@[reassoc]
lemma comp_average {X Y Z : Mod_ M A} (f : X ⟶ Y) (g : Y.X ⟶ Z.X) :
    f ≫ average S g = average S (f.hom ≫ g) := by
  apply Mod_.Hom.ext
  change f.hom ≫ (section_ S Y ≫ (A ⊴ₗ g) ≫ γ[A,Z.X]) =
    section_ S X ≫ (A ⊴ₗ (f.hom ≫ g)) ≫ γ[A,Z.X]
  rw [section_naturality_assoc, actionHomRight_comp, assoc]

@[reassoc]
lemma average_comp {X Y Z : Mod_ M A} (f : X.X ⟶ Y.X) (g : Y ⟶ Z) :
    average S f ≫ g = average S (f ≫ g.hom) := by
  apply Mod_.Hom.ext
  change (section_ S X ≫ (A ⊴ₗ f) ≫ γ[A,Y.X]) ≫ g.hom =
    section_ S X ≫ (A ⊴ₗ (f ≫ g.hom)) ≫ γ[A,Z.X]
  rw [assoc, assoc, IsMod_Hom.smul_hom, actionHomRight_comp, assoc]

/-- The actual free module for an arbitrary native algebra action. -/
def free (X : M) : Mod_ M A :=
  evaluate X (InternalModule.free (actionAlgebra (M := M) (A := A))
    (mop ((Functor.const M).obj X)))

@[simp] lemma free_X (X : M) : (free (A := A) X).X = A ⊙ₗ X := rfl

@[simp] lemma free_smul (X : M) :
    γ[A,(free (A := A) X).X] = (αₗ A A X).inv ≫ μ[A] ⊵ₗ X := by
  change 𝟙 _ ≫ ((αₗ A A X).inv ≫ μ[A] ⊵ₗ X) = _
  exact id_comp _

/-- Actual free extension of an arbitrary underlying morphism. -/
def freeLift {Y : Mod_ M A} {X : M} (f : X ⟶ Y.X) : free X ⟶ Y :=
  evaluateMap X (InternalModule.freeLift (M := constant Y) (Quiver.Hom.mop
    { app := fun _ => f
      naturality := by intro m n g; simp }))

@[simp] lemma freeLift_hom {Y : Mod_ M A} {X : M} (f : X ⟶ Y.X) :
    (freeLift f).hom = (A ⊴ₗ f) ≫ γ[A,Y.X] := rfl

@[reassoc]
lemma freeLift_comp {X Y : Mod_ M A} {Z : M} (f : Z ⟶ X.X) (g : X ⟶ Y) :
    freeLift f ≫ g = freeLift (f ≫ g.hom) := by
  apply Mod_.Hom.ext
  change ((A ⊴ₗ f) ≫ γ[A,X.X]) ≫ g.hom = (A ⊴ₗ (f ≫ g.hom)) ≫ γ[A,Y.X]
  rw [assoc, IsMod_Hom.smul_hom, actionHomRight_comp, assoc]

@[simp]
lemma unit_freeLift {Y : Mod_ M A} {X : M} (f : X ⟶ Y.X) :
    (λₗ[C] X).inv ≫ η[A] ⊵ₗ X ≫ (freeLift f).hom = f := by
  rw [freeLift_hom, ← action_exchange_assoc, ModObj.one_smul,
    ← actionUnitIso_hom_naturality, Iso.inv_hom_id_assoc]

instance forget_faithful : (Mod_.forget (D := M) A).Faithful where
  map_injective h := Mod_.Hom.ext h

/-- The genuine free-module unit detects underlying monomorphisms. -/
instance forget_preservesMonomorphisms :
    (Mod_.forget (D := M) A).PreservesMonomorphisms where
  preserves {X Y} f _ := by
    constructor
    intro Z g h eq
    change g ≫ f.hom = h ≫ f.hom at eq
    have hh : freeLift g = freeLift h := by
      apply (cancel_mono f).mp
      rw [freeLift_comp, freeLift_comp, eq]
    have hu := congrArg (fun k : free (A := A) Z ⟶ X =>
      (λₗ[C] Z).inv ≫ η[A] ⊵ₗ Z ≫ k.hom) hh
    simpa only [unit_freeLift] using hu

/-- The actual free-module functor for the native action. -/
def freeFunctor : M ⥤ Mod_ M A where
  obj := free
  map {X Y} f := evaluateMap X (InternalModule.freeMap
    (A := actionAlgebra (M := M) (A := A))
    (X := mop ((Functor.const M).obj X)) (Y := mop ((Functor.const M).obj Y))
    (Quiver.Hom.mop
      { app := fun _ => f
        naturality := by intro m n g; simp }))
  map_id X := by
    apply Mod_.Hom.ext
    change A ⊴ₗ 𝟙 X = 𝟙 _
    simp
  map_comp f g := by apply Mod_.Hom.ext; exact actionHomRight_comp A f g

/-- The free-module action map. -/
def actionHom (X : Mod_ M A) : free X.X ⟶ X := freeLift (𝟙 X.X)

@[simp] lemma actionHom_hom (X : Mod_ M A) : (actionHom X).hom = γ[A,X.X] := by
  change (A ⊴ₗ 𝟙 X.X) ≫ γ[A,X.X] = γ[A,X.X]
  simp

/-- The genuine section of the free-module action map. -/
def sectionHom (X : Mod_ M A) : X ⟶ free X.X :=
  evaluateMap X.X ((actionSeparable (M := M) S).moduleSectionHom (constant X))

@[simp] lemma sectionHom_hom (X : Mod_ M A) :
    (sectionHom S X).hom = section_ S X := rfl

/-- Every external module is an actual retract of the actual free module. -/
def freeRetract (X : Mod_ M A) : Retract X (free X.X) where
  i := sectionHom S X
  r := actionHom X
  retract := by
    apply Mod_.Hom.ext
    change section_ S X ≫ (actionHom X).hom = 𝟙 X.X
    rw [actionHom_hom, section_action]

end Paper18.Category.ModuleFunctor.SeparableAction
