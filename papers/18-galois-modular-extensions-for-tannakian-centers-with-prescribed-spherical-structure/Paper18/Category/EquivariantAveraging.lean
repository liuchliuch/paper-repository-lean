import Paper18.Category.EquivariantBiproducts

/-!
# Characteristic-zero averaging in equivariant categories

Averaging actual underlying morphisms over the finite group projects them
to equivariant morphisms and preserves compositions with equivariant maps.
Consequently actual underlying split monomorphisms and epimorphisms split
equivariantly. These are construction theorems, not semisimplicity axioms.
-/

noncomputable section
open Classical CategoryTheory CategoryTheory.Limits
open scoped BigOperators
universe v u w
namespace Paper18.Category.WeakAction
variable {G : Type w} [Group G] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear ℂ C]
  (A : WeakAction G C) [∀ g : G, (A.ρ g).Additive] [∀ g : G, (A.ρ g).Linear ℂ]

namespace Equivariant

omit [Preadditive C] [Linear ℂ C]
  [∀ g : G, (A.ρ g).Additive] [∀ g : G, (A.ρ g).Linear ℂ] in
/-- The inverse form of the equivariant multiplication condition. -/
theorem structureIso_inv_mul (X : A.Equivariant) (g h : G) :
    (X.structureIso g).inv ≫ (A.ρ g).map (X.structureIso h).inv =
      (X.structureIso (g * h)).inv ≫ (A.mulIso g h).inv.app X.obj := by
  have e : (A.ρ g).mapIso (X.structureIso h) ≪≫ X.structureIso g =
      (A.mulIso g h).app X.obj ≪≫ X.structureIso (g * h) :=
    Iso.ext (X.mul g h)
  exact congrArg Iso.inv e

/-- Conjugation of an actual underlying morphism by equivariant structures,
as a complex-linear map on the actual Hom space. -/
def conjugate (X Y : A.Equivariant) (g : G) : (X.obj ⟶ Y.obj) →ₗ[ℂ] (X.obj ⟶ Y.obj) where
  toFun f := (X.structureIso g).inv ≫ (A.ρ g).map f ≫ (Y.structureIso g).hom
  map_add' f h := by simp [Preadditive.add_comp, Preadditive.comp_add]
  map_smul' c f := by simp

@[simp]
theorem conjugate_apply (X Y : A.Equivariant) (g : G) (f : X.obj ⟶ Y.obj) :
    conjugate A X Y g f = (X.structureIso g).inv ≫ (A.ρ g).map f ≫
      (Y.structureIso g).hom := rfl

/-- Equivariant maps are precisely the invariant underlying maps. -/
theorem conjugate_eq_iff (X Y : A.Equivariant) (g : G) (f : X.obj ⟶ Y.obj) :
    conjugate A X Y g f = f ↔
      (A.ρ g).map f ≫ (Y.structureIso g).hom = (X.structureIso g).hom ≫ f := by
  constructor
  · intro h
    simpa [conjugate, Category.assoc] using (X.structureIso g).hom ≫= h
  · intro h
    simp [conjugate, h]

@[simp]
theorem conjugate_equivariant {X Y : A.Equivariant} (f : X ⟶ Y) (g : G) :
    conjugate A X Y g f.hom = f.hom :=
  (conjugate_eq_iff A X Y g f.hom).mpr (f.comm g)

/-- The weak multiplication coherence gives an honest action on Hom
spaces, even though the original categorical action is weak. -/
theorem conjugate_mul (X Y : A.Equivariant) (g h : G) (f : X.obj ⟶ Y.obj) :
    conjugate A X Y g (conjugate A X Y h f) = conjugate A X Y (g * h) f := by
  simp only [conjugate_apply, Functor.map_comp, Category.assoc]
  rw [← Category.assoc (X.structureIso g).inv, structureIso_inv_mul A]
  simp only [Category.assoc]
  rw [Y.mul]
  erw [(A.mulIso g h).hom.naturality_assoc f]
  simp


/-- Conjugation preserves composition of underlying maps. -/
theorem conjugate_comp {X Y Z : A.Equivariant} (g : G)
    (f : X.obj ⟶ Y.obj) (h : Y.obj ⟶ Z.obj) :
    conjugate A X Z g (f ≫ h) = conjugate A X Y g f ≫ conjugate A Y Z g h := by
  simp [conjugate, Functor.map_comp, Category.assoc]

section Finite
variable [Fintype G]

/-- The characteristic-zero average of actual conjugate morphisms. -/
def averageUnderlying (X Y : A.Equivariant) (f : X.obj ⟶ Y.obj) : X.obj ⟶ Y.obj :=
  (Fintype.card G : ℂ)⁻¹ • ∑ g : G, conjugate A X Y g f

/-- The average is invariant under the Hom-space action. -/
theorem averageUnderlying_invariant (X Y : A.Equivariant)
    (f : X.obj ⟶ Y.obj) (g : G) :
    conjugate A X Y g (averageUnderlying A X Y f) = averageUnderlying A X Y f := by
  unfold averageUnderlying
  rw [map_smul, map_sum]
  simp_rw [conjugate_mul]
  congr 1
  exact Function.Bijective.sum_comp (Group.mulLeft_bijective g)
    (fun h => conjugate A X Y h f)

/-- Averaging produces an actual equivariant morphism. -/
def average {X Y : A.Equivariant} (f : X.obj ⟶ Y.obj) : X ⟶ Y where
  hom := averageUnderlying A X Y f
  comm g := (conjugate_eq_iff A X Y g _).mp (averageUnderlying_invariant A X Y f g)

/-- Averaging fixes every equivariant morphism. -/
@[simp]
theorem average_hom {X Y : A.Equivariant} (f : X ⟶ Y) : average A f.hom = f := by
  apply Hom.ext
  change (Fintype.card G : ℂ)⁻¹ • ∑ g : G, conjugate A X Y g f.hom = f.hom
  simp only [conjugate_equivariant, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀, one_smul]
  exact_mod_cast Fintype.card_ne_zero

/-- Averaging commutes with precomposition by an equivariant map. -/
theorem comp_average {X Y Z : A.Equivariant} (f : X ⟶ Y) (h : Y.obj ⟶ Z.obj) :
    f ≫ average A h = average A (f.hom ≫ h) := by
  apply Hom.ext
  change f.hom ≫ averageUnderlying A Y Z h = averageUnderlying A X Z (f.hom ≫ h)
  unfold averageUnderlying
  rw [Linear.comp_smul, Preadditive.comp_sum]
  simp only [conjugate_comp, conjugate_equivariant]

/-- Averaging commutes with postcomposition by an equivariant map. -/
theorem average_comp {X Y Z : A.Equivariant} (f : X.obj ⟶ Y.obj) (h : Y ⟶ Z) :
    average A f ≫ h = average A (f ≫ h.hom) := by
  apply Hom.ext
  change averageUnderlying A X Y f ≫ h.hom = averageUnderlying A X Z (f ≫ h.hom)
  unfold averageUnderlying
  rw [Linear.smul_comp, Preadditive.sum_comp]
  simp only [conjugate_comp, conjugate_equivariant]

/-- A chosen underlying retraction becomes an actual equivariant
retraction by averaging. -/
def splitMonoOfUnderlyingRetraction {X Y : A.Equivariant} (f : X ⟶ Y)
    (r : Y.obj ⟶ X.obj) (hr : f.hom ≫ r = 𝟙 X.obj) : SplitMono f where
  retraction := average A r
  id := by rw [comp_average, hr]; exact average_hom A (𝟙 X)

/-- A chosen underlying section becomes an actual equivariant section. -/
def splitEpiOfUnderlyingSection {X Y : A.Equivariant} (f : X ⟶ Y)
    (s : Y.obj ⟶ X.obj) (hs : s ≫ f.hom = 𝟙 Y.obj) : SplitEpi f where
  section_ := average A s
  id := by rw [average_comp, hs]; exact average_hom A (𝟙 Y)

end Finite
end Equivariant
end Paper18.Category.WeakAction
