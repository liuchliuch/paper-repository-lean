import Paper18.Category.RadfordBraidedTrace
import Paper18.Category.PivotalDimension
import Paper18.Category.SemisimpleSplitting

/-!
# Nondegenerate categorical traces and the Radford square criterion

Nonvanishing of simple dimensions and actual simple decompositions give a
nondegenerate trace pairing on arbitrary Hom spaces. Consequently actual
sphericality implies the canonical Radford square equation, complementing the
previous direct proof of the converse.
-/
noncomputable section
universe v u w
namespace Paper18.Category
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
namespace PivotalStructure
variable (J : PivotalStructure C)
include S

/-- The actual categorical trace pairing is nondegenerate in every Hom
space of a finite semisimple rigid category. -/
lemma rightTrace_nondegenerate {X Y : C} (f : X ⟶ Y)
    (h : ∀ g : Y ⟶ X, J.rightTrace (f ≫ g) = 0) : f = 0 := by
  apply S.hom_ext_simples
  intro i a
  simp only [comp_zero]
  apply S.hom_ext_to_simples
  intro j b
  simp only [zero_comp]
  by_contra hn
  let q : S.simpleObject i ⟶ S.simpleObject j := (a ≫ f) ≫ b
  have hq : q ≠ 0 := hn
  letI : IsIso q := isIso_of_hom_simple hq
  have ht := h (b ≫ inv q ≫ a)
  have ht' : J.rightTrace ((f ≫ b ≫ inv q) ≫ a) = 0 := by
    simpa only [assoc] using ht
  rw [J.rightTrace_comp] at ht'
  have hi : a ≫ (f ≫ b ≫ inv q) = 𝟙 (S.simpleObject i) := by
    simpa only [q, assoc] using IsIso.hom_inv_id q
  rw [hi] at ht'
  apply J.rightDim_ne_zero S (S.simpleObject i)
  change unitScalarEquiv (C := C) (J.rightTrace (𝟙 (S.simpleObject i))) = 0
  rw [ht', map_zero]

/-- Actual morphisms are determined by all their categorical trace
pairings, not only by their numerical dimensions. -/
lemma rightTrace_ext {X Y : C} (f g : X ⟶ Y)
    (h : ∀ k : Y ⟶ X, J.rightTrace (f ≫ k) = J.rightTrace (g ≫ k)) : f = g := by
  apply sub_eq_zero.mp
  apply J.rightTrace_nondegenerate S
  intro k
  rw [Preadditive.sub_comp]
  change J.rightTraceAddHom X (f ≫ k - g ≫ k) = 0
  rw [map_sub]
  change J.rightTrace (f ≫ k) - J.rightTrace (g ≫ k) = 0
  rw [h k, sub_self]

variable [BraidedCategory C]

/-- Actual sphericality forces the canonical Radford square equation for
every actual object. -/
lemma radfordSquare_of_spherical (hJ : J.Spherical) (X : C) :
    J.j.hom.app X ≫ (doubleDualFunctor C).map (J.j.hom.app X) =
      (braidedFourDualIso X).hom := by
  let q : X ⟶ (doubleDualFunctor C).obj X :=
    (braidedFourDualIso X).hom ≫ (doubleDualFunctor C).map (J.j.inv.app X)
  let k : X ⟶ X := q ≫ J.j.inv.app X
  have hk : k ≫ J.j.hom.app X = q := by
    dsimp only [k]
    simp only [assoc, Iso.inv_hom_id_app, comp_id]
  have hk_id : k = 𝟙 X := by
    apply J.rightTrace_ext S
    intro f
    rw [J.rightTrace_comp]
    calc
      J.rightTrace (f ≫ k) = η_ X (dual C X) ≫
          f ▷ dual C X ≫ q ▷ dual C X ≫ ε_ (dual C X) (dual C (dual C X)) := by
        calc
          _ = η_ X (dual C X) ≫ (f ≫ k ≫ J.j.hom.app X) ▷ dual C X ≫
              ε_ (dual C X) (dual C (dual C X)) := by
            simp only [rightTrace, leftEvaluation, comp_whiskerRight, assoc]
          _ = _ := by rw [hk, comp_whiskerRight, assoc]
      _ = J.leftTrace f := by
        have ht := braidedFourDual_trace X (J.j.app X) f
        simpa only [leftTrace, leftCoevaluation, assoc, q] using ht.symm
      _ = J.rightTrace f := hJ X f
      _ = J.rightTrace (𝟙 X ≫ f) := by rw [id_comp]
  have hq : q = J.j.hom.app X := by
    rw [← hk, hk_id, id_comp]
  have he := congrArg (fun t => t ≫ (doubleDualFunctor C).map (J.j.hom.app X)) hq
  dsimp only [q] at he
  simp only [assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id] at he
  exact he.symm.trans (Category.comp_id _)

/-- Sphericality of a coherent actual pivotal structure is equivalent to
the actual Radford square equation, object by object. -/
lemma spherical_iff_radfordSquare : J.Spherical ↔
    ∀ X : C, J.j.hom.app X ≫ (doubleDualFunctor C).map (J.j.hom.app X) =
      (braidedFourDualIso X).hom := by
  constructor
  · exact J.radfordSquare_of_spherical S
  · intro h X f
    have ht := braidedFourDual_trace_of_square X (J.j.app X) (h X) f
    simpa only [leftTrace, leftCoevaluation, rightTrace, leftEvaluation, assoc] using ht

end PivotalStructure
end Paper18.Category
