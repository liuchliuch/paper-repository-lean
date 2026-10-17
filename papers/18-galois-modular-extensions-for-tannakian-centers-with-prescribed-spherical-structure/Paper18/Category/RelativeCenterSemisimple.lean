import Paper18.Category.RelativeCenterAugmentationUnit
import Paper18.Category.SemisimpleGenerator

/-! # Actual finite semisimplicity of the actual relative center -/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u w
namespace Paper18.Category.RelativeCenter
open Drinfeld
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [Simple (𝟙_ C)] [BraidedCategory C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {P : ObjectProperty C} [P.IsMonoidal] [IsAdditiveFullProperty P]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι) (J : PivotalStructure C)

lemma simple_receives_induction (Z : RelativeCenter P) [Simple Z] :
    ∃ i : ι, ∃ h : (restriction P).obj (inductionObj S J (S.simpleObject i)) ⟶ Z, h ≠ 0 := by
  have hn : (𝟙 Z.1) ≠ 0 := by
    intro h
    apply CategoryTheory.id_nonzero Z
    apply ext P
    exact h
  have hg : ∃ i : ι, ∃ g : S.simpleObject i ⟶ Z.1, g ≠ 0 := by
    by_contra h
    apply hn
    apply S.hom_ext_simples
    intro i g
    have hz : g = 0 := by
      by_contra hgn
      exact h ⟨i, g, hgn⟩
    simp only [hz, zero_comp, comp_id]
  obtain ⟨i, g, hg⟩ := hg
  refine ⟨i, augmentationHom S J Z g, ?_⟩
  intro hh
  apply hg
  have he := congrArg (fun k => inductionAdjunctionUnit J S (S.simpleObject i) ≫ k)
    (congrArg Hom.f hh)
  change inductionAdjunctionUnit J S (S.simpleObject i) ≫ augmentation S J Z g = _ at he
  simpa only [adjunctionUnit_augmentation, zero_f, comp_zero] using he

/-- The induction objects form an actual finite simple generator as soon
as the actual simple decompositions are available. -/
def generatorOfSimpleDecompositions (D : SimpleDecompositions (RelativeCenter P)) :
    FiniteSimpleGenerator (RelativeCenter P) ι where
  obj i := (restriction P).obj (inductionObj S J (S.simpleObject i))
  covers Z hZ := by
    letI := hZ
    obtain ⟨i, h, hh⟩ := simple_receives_induction S J Z
    let e := D.iso ((restriction P).obj (inductionObj S J (S.simpleObject i)))
    have he : e.inv ≫ h ≠ 0 := by
      intro hz
      apply hh
      have ht := congrArg (fun k => e.hom ≫ k) hz
      simpa only [← assoc, Iso.hom_inv_id, id_comp, comp_zero] using ht
    have ha : ∃ a, biproduct.ι (D.family ((restriction P).obj (inductionObj S J (S.simpleObject i)))) a ≫
        e.inv ≫ h ≠ 0 := by
      by_contra hn
      apply he
      apply biproduct.hom_ext'
      intro a
      simpa only [assoc, comp_zero, not_not] using not_exists.mp hn a
    obtain ⟨a, ha⟩ := ha
    let k := biproduct.ι (D.family ((restriction P).obj (inductionObj S J (S.simpleObject i)))) a ≫ e.inv ≫ h
    letI := D.simple ((restriction P).obj (inductionObj S J (S.simpleObject i))) a
    letI := CategoryTheory.isIso_of_hom_simple ha
    refine ⟨i, ⟨{
      i := inv k ≫ biproduct.ι (D.family ((restriction P).obj (inductionObj S J (S.simpleObject i)))) a ≫ e.inv
      r := h
      retract := ?_ }⟩⟩
    rw [assoc, assoc]
    exact IsIso.inv_hom_id k

def simpleDecompositions : SimpleDecompositions (RelativeCenter P) :=
  SimpleDecompositions.ofSplitMonos (splitMono S J)

def finiteSimpleGenerator : FiniteSimpleGenerator (RelativeCenter P) ι :=
  generatorOfSimpleDecompositions S J (simpleDecompositions S J)

def SimpleIndex : Type w :=
  (simpleDecompositions (P := P) S J).SimpleIndex (finiteSimpleGenerator (P := P) S J)

instance simpleIndex_fintype : Fintype (SimpleIndex (P := P) S J) := by
  dsimp only [SimpleIndex]
  infer_instance

/-- The finite actual relative-center skeleton is constructed, not assumed. -/
def skeleton : FiniteSemisimpleSkeleton (RelativeCenter P) (SimpleIndex (P := P) S J) :=
  (simpleDecompositions S J).skeleton (finiteSimpleGenerator S J)

end Paper18.Category.RelativeCenter
