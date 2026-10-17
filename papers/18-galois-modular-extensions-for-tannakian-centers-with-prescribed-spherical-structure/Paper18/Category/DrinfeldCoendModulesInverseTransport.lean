import Paper18.Category.Semisimple
import Mathlib.CategoryTheory.Functor.EpiMono

/-! # Actual finite semisimple skeletons transported along additive equivalences -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe v u v' u' w
namespace Paper18.Category.DrinfeldCoendModules.SkeletonTransport
variable {C : Type u} [Category.{v} C] [Preadditive C]
  {E : Type u'} [Category.{v'} E] [Preadditive E]
  (F : C ⥤ E) [F.Additive] [F.IsEquivalence]

/-- An additive categorical equivalence preserves categorical simplicity,
by lifting arbitrary target monomorphisms to the source. -/
lemma simple_image (X : C) [Simple X] : Simple (F.obj X) := by
  have hid : 𝟙 (F.obj X) ≠ 0 := by
    intro hz
    apply CategoryTheory.id_nonzero X
    apply F.map_injective
    simpa using hz
  refine ⟨fun {Y} f _ => ?_⟩
  constructor
  · intro hi hz
    letI := hi
    apply hid
    calc
      𝟙 (F.obj X) = inv f ≫ f := (IsIso.inv_hom_id f).symm
      _ = inv f ≫ 0 := congrArg (fun q : Y ⟶ F.obj X => inv f ≫ q) hz
      _ = 0 := comp_zero
  · intro hf
    let e := F.objObjPreimageIso Y
    let g := F.preimage (e.hom ≫ f)
    have hg : F.map g = e.hom ≫ f := F.map_preimage _
    letI : Mono (F.map g) := by rw [hg]; infer_instance
    letI : Mono g := F.mono_of_mono_map inferInstance
    have hgz : g ≠ 0 := by
      intro hz
      apply hf
      apply (cancel_epi e.hom).mp
      rw [← hg, hz, F.map_zero, comp_zero]
    letI : IsIso g := isIso_of_mono_of_nonzero hgz
    have he : f = e.inv ≫ F.map g := by rw [hg, Iso.inv_hom_id_assoc]
    rw [he]
    infer_instance

variable [HasFiniteBiproducts C] [HasFiniteBiproducts E]
  {ι : Type w} [Fintype ι] (T : FiniteSemisimpleSkeleton C ι)

/-- Actual simple representatives and actual finite biproduct decompositions
are carried along the actual additive equivalence. -/
def skeleton : FiniteSemisimpleSkeleton E ι where
  simpleObject i := F.obj (T.simpleObject i)
  simple i := by letI := T.simple i; exact simple_image F (T.simpleObject i)
  iso_injective i j e := T.iso_injective i j ⟨F.preimageIso e.some⟩
  length Z := T.length (F.objPreimage Z)
  label Z := T.label (F.objPreimage Z)
  decomposition Z :=
    (F.objObjPreimageIso Z).symm ≪≫ F.mapIso (T.decomposition (F.objPreimage Z)) ≪≫
      F.mapBiproduct (fun a => T.simpleObject (T.label (F.objPreimage Z) a))

end Paper18.Category.DrinfeldCoendModules.SkeletonTransport
