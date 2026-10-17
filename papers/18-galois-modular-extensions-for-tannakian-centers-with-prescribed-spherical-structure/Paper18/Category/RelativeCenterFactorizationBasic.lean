import Paper18.Category.RelativeCenterSemisimple
import Paper18.Category.RelativeCenterRigid
import Paper18.Category.Factorization

/-! # Actual positive-negative Hom blocks in the relative center -/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits
open CategoryTheory.BraidedCategory
universe v u w
namespace Paper18.Category.RelativeCenter
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [Simple (𝟙_ C)] [BraidedCategory C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  (P : ObjectProperty C) [P.IsMonoidal]

def positive : C ⥤ RelativeCenter P := Drinfeld.positive C ⋙ restriction P
def negative : C ⥤ RelativeCenter P := Drinfeld.negative C ⋙ restriction P

instance positive_monoidal : (positive P).Monoidal := by unfold positive; infer_instance
instance negative_monoidal : (negative P).Monoidal := by unfold negative; infer_instance
instance positive_additive : (positive P).Additive := by unfold positive; infer_instance
instance negative_additive : (negative P).Additive := by unfold negative; infer_instance
instance positive_linear : (positive P).Linear ℂ := by unfold positive; infer_instance
instance negative_linear : (negative P).Linear ℂ := by unfold negative; infer_instance
instance positive_faithful : (positive P).Faithful where
  map_injective h := congrArg Hom.f h
instance negative_faithful : (negative P).Faithful where
  map_injective h := congrArg Hom.f h
instance positive_full : (positive P).Full where
  map_surjective f := ⟨f.f, by apply ext P; rfl⟩
instance negative_full : (negative P).Full where
  map_surjective f := ⟨f.f, by apply ext P; rfl⟩
instance positive_simple (X : C) [Simple X] : Simple ((positive P).obj X) := by
  letI : Simple (((positive P).obj X).1) := inferInstanceAs (Simple X)
  exact simple_of_underlying_simple _
instance negative_simple (X : C) [Simple X] : Simple ((negative P).obj X) := by
  letI : Simple (((negative P).obj X).1) := inferInstanceAs (Simple X)
  exact simple_of_underlying_simple _

/-- Actual centralization gives the actual positive-negative comparison in
the relative center, with identity underlying map. -/
def positiveNegativeIso (X : C) (hX : X ∈ centralizer (P : Set C)) :
    (positive P).obj X ≅ (negative P).obj X :=
  by
    let f : (positive P).obj X ⟶ (negative P).obj X := {
      f := 𝟙 X
      comm U hU := by
        change (𝟙 X ▷ U) ≫ (β_ U X).inv = (β_ X U).hom ≫ U ◁ 𝟙 X
        simp only [id_whiskerRight, id_comp, whiskerLeft_id, comp_id]
        apply (cancel_mono (β_ U X).hom).mp
        rw [Iso.inv_hom_id]
        exact Eq.symm (hX U hU) }
    letI : IsIso f.f := inferInstanceAs (IsIso (𝟙 X))
    exact isoMk P f

variable {P} [IsAdditiveFullProperty P]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

lemma positive_negative_simple_nonzero {i j : ι}
    (f : (positive P).obj (S.simpleObject i) ⟶ (negative P).obj (S.simpleObject j))
    (hf : f ≠ 0) : i = j ∧ S.simpleObject i ∈ centralizer (P : Set C) := by
  have hfu : f.f ≠ 0 := by
    intro h
    apply hf
    apply ext P
    exact h
  letI : IsIso f.f := CategoryTheory.isIso_of_hom_simple
    (X := S.simpleObject i) (Y := S.simpleObject j) hfu
  have hij := S.iso_injective i j ⟨asIso f.f⟩
  refine ⟨hij, ?_⟩
  subst j
  intro U hU
  have hc := f.comm U hU
  change (f.f ▷ U) ≫ (β_ U (S.simpleObject i)).inv =
    (β_ (S.simpleObject i) U).hom ≫ U ◁ f.f at hc
  have hn := braiding_naturality_left f.f U
  change (f.f ▷ U) ≫ (β_ (S.simpleObject i) U).hom =
    (β_ (S.simpleObject i) U).hom ≫ U ◁ f.f at hn
  rw [← hn] at hc
  have he := (cancel_epi (f.f ▷ U)).mp hc
  change (β_ (S.simpleObject i) U).hom ≫ (β_ U (S.simpleObject i)).hom = 𝟙 _
  rw [← he, Iso.inv_hom_id]

lemma finrank_positive_negative_simple (i j : ι) :
    Module.finrank ℂ ((positive P).obj (S.simpleObject i) ⟶ (negative P).obj (S.simpleObject j)) =
      if i = j ∧ S.simpleObject j ∈ centralizer (P : Set C) then 1 else 0 := by
  by_cases h : i = j ∧ S.simpleObject j ∈ centralizer (P : Set C)
  · rcases h with ⟨hij, h⟩
    subst i
    rw [if_pos ⟨rfl, h⟩,
      finrank_hom_iso (Iso.refl _) (positiveNegativeIso P (S.simpleObject j) h).symm]
    exact CategoryTheory.finrank_endomorphism_simple_eq_one ℂ ((positive P).obj (S.simpleObject j))
  · have hz (f : (positive P).obj (S.simpleObject i) ⟶ (negative P).obj (S.simpleObject j)) : f = 0 := by
      by_contra hf
      obtain ⟨hij, hi⟩ := positive_negative_simple_nonzero S f hf
      exact h ⟨hij, hij ▸ hi⟩
    letI : Subsingleton ((positive P).obj (S.simpleObject i) ⟶ (negative P).obj (S.simpleObject j)) :=
      ⟨fun f g => (hz f).trans (hz g).symm⟩
    rw [Module.finrank_zero_of_subsingleton, if_neg h]

variable [RightRigidCategory (RelativeCenter P)]

/-- The unit multiplicity of a positive-negative pair is exactly the actual
centralizer support on its dual diagonal. -/
lemma finrank_unit_positive_negative (i j : ι) :
    Module.finrank ℂ ((𝟙_ (RelativeCenter P)) ⟶
      (positive P).obj (S.simpleObject i) ⊗ (negative P).obj (S.simpleObject j)) =
      if S.dualLabel i = j ∧ S.simpleObject j ∈ centralizer (P : Set C) then 1 else 0 := by
  let A := (positive P).obj (S.simpleObject i)
  let B := (negative P).obj (S.simpleObject j)
  let e : (positive P).obj (S.simpleObject (S.dualLabel i)) ≅ dual (RelativeCenter P) A :=
    (positive P).mapIso (S.dualIso i) ≪≫ dualComparison (positive P) (S.simpleObject i)
  calc
    _ = Module.finrank ℂ (dual (RelativeCenter P) A ⊗ (𝟙_ (RelativeCenter P)) ⟶ B) :=
      (tensorLeftHomLinearEquiv (𝟙_ (RelativeCenter P)) A (dual (RelativeCenter P) A) B).finrank_eq.symm
    _ = Module.finrank ℂ ((positive P).obj (S.simpleObject (S.dualLabel i)) ⟶ B) :=
      finrank_hom_iso ((ρ_ (dual (RelativeCenter P) A)) ≪≫ e.symm) (Iso.refl B)
    _ = _ := finrank_positive_negative_simple S (S.dualLabel i) j

end Paper18.Category.RelativeCenter
