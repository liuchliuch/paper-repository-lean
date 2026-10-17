import Paper18.Category.DrinfeldSemisimpleNaturality
import Paper18.Category.DrinfeldExact
import Paper18.Category.SemisimpleGenerator

/-! # Finiteness of the actual central simple family from induction

Once actual finite simple decompositions have been constructed, the actual
induction adjunction makes the finitely many induced underlying simples a
finite categorical generator. This step does not assume a finite center
skeleton or any numerical center-dimension formula.
-/
noncomputable section
universe v u w
namespace Paper18.Category.Drinfeld
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open Classical
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [LeftRigidCategory C] [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι) (J : PivotalStructure C)

omit [LeftRigidCategory C] [Simple (𝟙_ C)] in
lemma center_simple_receives_induction (Z : Center C) [Simple Z] :
    ∃ i : ι, ∃ h : inductionObj S J (S.simpleObject i) ⟶ Z, h ≠ 0 := by
  have hn : (𝟙 Z.1) ≠ 0 := by
    intro h
    apply CategoryTheory.id_nonzero Z
    apply Center.ext
    exact h
  have hg : ∃ i : ι, ∃ g : S.simpleObject i ⟶ Z.1, g ≠ 0 := by
    by_contra h
    apply hn
    apply S.hom_ext_simples
    intro i g
    have hz : g = 0 := by
      by_contra hn
      exact h ⟨i, g, hn⟩
    simp only [hz, zero_comp, comp_id]
  obtain ⟨i, g, hg⟩ := hg
  let h := (inductionHomLinearEquiv S J (S.simpleObject i) Z).symm g
  refine ⟨i, h, ?_⟩
  intro hh
  apply hg
  have he := congrArg (inductionHomLinearEquiv S J (S.simpleObject i) Z) hh
  simpa only [h, LinearEquiv.apply_symm_apply, map_zero] using he

/-- The induction objects form an actual finite simple generator as soon
as the actual simple decompositions are available. -/
def centerGeneratorOfSimpleDecompositions (D : SimpleDecompositions (Center C)) :
    FiniteSimpleGenerator (Center C) ι where
  obj i := inductionObj S J (S.simpleObject i)
  covers Z hZ := by
    letI := hZ
    obtain ⟨i, h, hh⟩ := center_simple_receives_induction S J Z
    let e := D.iso (inductionObj S J (S.simpleObject i))
    have he : e.inv ≫ h ≠ 0 := by
      intro hz
      apply hh
      have ht := congrArg (fun k => e.hom ≫ k) hz
      simpa only [← assoc, Iso.hom_inv_id, id_comp, comp_zero] using ht
    have ha : ∃ a, biproduct.ι (D.family (inductionObj S J (S.simpleObject i))) a ≫
        e.inv ≫ h ≠ 0 := by
      by_contra hn
      apply he
      apply biproduct.hom_ext'
      intro a
      simpa only [assoc, comp_zero, not_not] using not_exists.mp hn a
    obtain ⟨a, ha⟩ := ha
    let k := biproduct.ι (D.family (inductionObj S J (S.simpleObject i))) a ≫ e.inv ≫ h
    letI := D.simple (inductionObj S J (S.simpleObject i)) a
    letI := CategoryTheory.isIso_of_hom_simple ha
    refine ⟨i, ⟨{
      i := inv k ≫ biproduct.ι (D.family (inductionObj S J (S.simpleObject i))) a ≫ e.inv
      r := h
      retract := ?_ }⟩⟩
    rw [assoc, assoc]
    exact IsIso.inv_hom_id k

end Paper18.Category.Drinfeld
