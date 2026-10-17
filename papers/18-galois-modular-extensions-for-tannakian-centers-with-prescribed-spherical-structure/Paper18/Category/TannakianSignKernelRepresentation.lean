import Paper18.Category.TannakianSignKernelCharacterElement
import Paper18.Category.TannakianSignKernelQuotient
import Paper18.Category.SignKernelBasic
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-! # Actual quotient representations realize the actual positive representation kernel -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace Paper18.Category.TannakianSignKernel
variable {G : Type} [Group G] [Fintype G]
  (χ : 𝟭 (FDRep ℂ G) ≅ 𝟭 (FDRep ℂ G)) [NatTrans.IsMonoidal χ.hom]

/-- The actual normal subgroup killed by positive representations. Centrality
of the recovered generator was proved from actual naturality. -/
def annihilator : Subgroup G := Subgroup.normalClosure {characterElement χ}

instance annihilator_normal : (annihilator χ).Normal := by
  dsimp [annihilator]; infer_instance

abbrev KernelGroup := G ⧸ annihilator χ

instance kernelGroup_fintype : Fintype (KernelGroup χ) := Fintype.ofFinite _

/-- The actual component equation is precisely the actual quotient descent equation. -/
lemma trivialOn_iff_component_id (V : FDRep ℂ G) :
    TrivialOn (annihilator χ) V ↔ χ.hom.app V = 𝟙 V := by
  have he : χ.hom.app V = 𝟙 V ↔ V.ρ (characterElement χ) = 1 := by
    constructor
    · intro h
      rw [← component_eq_action χ V]
      exact congrArg (fun k : V ⟶ V => k.hom.hom) h
    · intro h
      apply Action.Hom.ext
      apply ModuleCat.hom_ext
      change (χ.hom.app V).hom.hom = 1
      rw [component_eq_action, h]
  rw [he]
  constructor
  · intro h
    exact h _ (Subgroup.subset_normalClosure (Set.mem_singleton _))
  · intro h
    have hN : annihilator χ ≤ V.ρ.ker := by
      apply Subgroup.normalClosure_le_normal
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst g
      exact h
    exact fun g hg => hN hg

/-- Actual quotient inflation, landing in the actual positive full subcategory. -/
def positiveInflate : FDRep ℂ (KernelGroup χ) ⥤ SignKernel.Positive χ :=
  ObjectProperty.lift (SignKernel.positiveProperty χ) (inflate (annihilator χ))
    (fun V => (SignKernel.mem_positive χ _).mpr
      ((trivialOn_iff_component_id χ _).mp (inflate_trivial (annihilator χ) V)))

instance positiveInflate_full : (positiveInflate χ).Full := by
  dsimp [positiveInflate]; infer_instance
instance positiveInflate_faithful : (positiveInflate χ).Faithful := by
  dsimp [positiveInflate]; infer_instance
instance positiveInflate_additive : (positiveInflate χ).Additive where
  map_add := by intros; rfl
instance positiveInflate_linear : (positiveInflate χ).Linear ℂ where
  map_smul := by intros; rfl

def positiveInflateCoreMonoidal : (positiveInflate χ).CoreMonoidal where
  εIso := (SignKernel.positiveProperty χ).isoMk
    (Functor.Monoidal.εIso (inflate (annihilator χ)))
  μIso X Y := (SignKernel.positiveProperty χ).isoMk
    (Functor.Monoidal.μIso (inflate (annihilator χ)) X Y)
  μIso_hom_natural_left f X := Functor.LaxMonoidal.μ_natural_left (inflate (annihilator χ)) f X
  μIso_hom_natural_right X f := Functor.LaxMonoidal.μ_natural_right (inflate (annihilator χ)) X f
  associativity X Y Z := Functor.LaxMonoidal.associativity (inflate (annihilator χ)) X Y Z
  left_unitality X := Functor.LaxMonoidal.left_unitality (inflate (annihilator χ)) X
  right_unitality X := Functor.LaxMonoidal.right_unitality (inflate (annihilator χ)) X

instance positiveInflate_monoidal : (positiveInflate χ).Monoidal :=
  (positiveInflateCoreMonoidal χ).toMonoidal

instance positiveInflate_braided : (positiveInflate χ).Braided where
  braided X Y := Functor.LaxBraided.braided (F := inflate (annihilator χ)) X Y

instance positiveInflate_essSurj : (positiveInflate χ).EssSurj where
  mem_essImage V := by
    have hV : TrivialOn (annihilator χ) V.obj :=
      (trivialOn_iff_component_id χ V.obj).mpr ((SignKernel.mem_positive χ _).mp V.property)
    exact ⟨quotientRepresentation (annihilator χ) V.obj hV,
      ⟨(SignKernel.positiveProperty χ).isoMk (inflateQuotientIso (annihilator χ) V.obj hV)⟩⟩

instance positiveInflate_isEquivalence : (positiveInflate χ).IsEquivalence where

/-- A genuine representation-theoretic realization of the positive tensor kernel. -/
def quotientEquivalence : FDRep ℂ (KernelGroup χ) ≌ SignKernel.Positive χ :=
  (positiveInflate χ).asEquivalence

instance quotientEquivalence_functor_braided : (quotientEquivalence χ).functor.Braided :=
  positiveInflate_braided χ
instance quotientEquivalence_functor_linear : (quotientEquivalence χ).functor.Linear ℂ :=
  positiveInflate_linear χ
instance quotientEquivalence_functor_additive : (quotientEquivalence χ).functor.Additive :=
  positiveInflate_additive χ

instance quotientEquivalence_inverse_monoidal : (quotientEquivalence χ).inverse.Monoidal :=
  (quotientEquivalence χ).inverseMonoidal
instance quotientEquivalence_isMonoidal : (quotientEquivalence χ).IsMonoidal := inferInstance
instance quotientEquivalence_unit_monoidal :
    NatTrans.IsMonoidal (quotientEquivalence χ).unitIso.hom :=
  inferInstanceAs (NatTrans.IsMonoidal (quotientEquivalence χ).unit)
instance quotientEquivalence_counit_monoidal :
    NatTrans.IsMonoidal (quotientEquivalence χ).counitIso.hom :=
  inferInstanceAs (NatTrans.IsMonoidal (quotientEquivalence χ).counit)
instance quotientEquivalence_inverse_linear : (quotientEquivalence χ).inverse.Linear ℂ :=
  Equivalence.inverseLinear ℂ (quotientEquivalence χ)
instance quotientEquivalence_inverse_additive : (quotientEquivalence χ).inverse.Additive :=
  Equivalence.inverse_additive (quotientEquivalence χ)

instance quotientEquivalence_inverse_braided : (quotientEquivalence χ).inverse.Braided where
  toMonoidal := quotientEquivalence_inverse_monoidal χ
  braided X Y := by
    letI : NatTrans.IsMonoidal (quotientEquivalence χ).counitIso.symm.hom :=
      inferInstanceAs (NatTrans.IsMonoidal (quotientEquivalence χ).counitIso.inv)
    letI : ((quotientEquivalence χ).inverse ⋙ (quotientEquivalence χ).functor).LaxBraided :=
      Functor.LaxBraided.ofNatIso (quotientEquivalence χ).counitIso.symm
    have h := Functor.LaxBraided.braided
      (F := (quotientEquivalence χ).inverse ⋙ (quotientEquivalence χ).functor) X Y
    apply (quotientEquivalence χ).functor.map_injective
    apply (cancel_epi (Functor.LaxMonoidal.μ (quotientEquivalence χ).functor
      ((quotientEquivalence χ).inverse.obj X) ((quotientEquivalence χ).inverse.obj Y))).mp
    simp only [Functor.map_comp]
    rw [Functor.LaxBraided.braided_assoc]
    simpa only [Functor.comp_map, Functor.comp_obj, Functor.LaxMonoidal.comp_μ,
      Category.assoc] using h

end Paper18.Category.TannakianSignKernel
