import Paper18.Category.CrossedBraidedGaugingRegularUnit
import Paper18.Category.CrossedBraidedGaugingBraided
import Paper18.Category.Braided

/-! # Actual transparent equivariant objects lie in the neutral component -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category.CrossedBraidedGauging.CrossedBraiding
variable {G : Type w} [Group G] [Fintype G]
  {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasFiniteBiproducts C] [HasKernels C]
  {P : Grading G C} {A : WeakAction G C}
  [∀ g : G, (A.ρ g).Monoidal] [A.IsMonoidal]
  [∀ g : G, (A.ρ g).Additive]
  {Q : GradedAction P A} (B : CrossedBraiding P A Q)

/-- Actual trivial monodromy with the regular unit kills every actual
nonidentity degree summand. No faithfulness or semisimplicity is needed. -/
theorem homogeneous_of_regularUnit_monodromy (E : A.Equivariant)
    (hc : (B.halfSwapIso E.obj (regularUnit (A := A))).hom ≫
      (B.halfSwapIso (regularUnit (A := A)).obj E).hom =
        𝟙 (E.obj ⊗ (regularUnit (A := A)).obj)) : P.Homogeneous 1 E.obj := by
  have hp (g : G) (hg : g ≠ 1) : (P.projection g).app E.obj = 0 := by
    let V := P.component g E.obj
    let i := P.componentInclusion g E.obj
    let I := regularUnit (A := A)
    have hm := congrArg
      (fun k => (V ◁ regularUnitInjection (A := A) 1) ≫ (i ▷ I.obj) ≫ k) hc
    simp only [Category.assoc, Category.comp_id] at hm
    erw [Category.comp_id] at hm
    change (V ◁ regularUnitInjection (A := A) 1) ≫
        (P.componentInclusion g E.obj ▷ I.obj) ≫
          (B.halfSwapIso E.obj I).hom ≫ (B.halfSwapIso I.obj E).hom = _ at hm
    rw [B.halfSwapIso_component_assoc] at hm
    rw [B.halfSwapIso_homogeneous 1 I.obj Q.regularUnit_homogeneous,
      ← B.neutralIso_eq_block] at hm
    rw [B.neutralIso_naturality_right I.obj Q.regularUnit_homogeneous
      (P.componentInclusion g E.obj)] at hm
    rw [B.regularUnit_monodromy_assoc g 1 V (P.component_homogeneous g E.obj)] at hm
    simp only [mul_one] at hm
    let sm : SplitMono (i ▷ I.obj) :=
      ⟨P.componentProjection g E.obj ▷ I.obj, by
        rw [← comp_whiskerRight]
        change (P.componentInclusion g E.obj ≫ P.componentProjection g E.obj) ▷ I.obj = _
        rw [P.componentInclusion_projection, id_whiskerRight]⟩
    letI : Mono (i ▷ I.obj) := sm.mono
    have he : V ◁ regularUnitInjection (A := A) g =
        V ◁ regularUnitInjection (A := A) 1 := (cancel_mono (i ▷ I.obj)).mp hm
    have he' := congrArg (fun k => k ≫ (V ◁ regularUnitProjection (A := A) 1)) he
    have hz : IsZero (V ⊗ 𝟙_ C) := by
      apply (IsZero.iff_id_eq_zero _).mpr
      have hzero : (0 : V ⊗ 𝟙_ C ⟶ V ⊗ 𝟙_ C) = 𝟙 (V ⊗ 𝟙_ C) := by
        simpa only [← whiskerLeft_comp, regularUnitInjection_projection,
          if_neg hg, if_pos rfl, if_true, MonoidalPreadditive.whiskerLeft_zero,
          whiskerLeft_id] using he'
      exact hzero.symm
    have hv : IsZero V := (ρ_ V).isZero_iff.mp hz
    rw [← P.componentProjection_inclusion g E.obj]
    have hi : P.componentInclusion g E.obj = 0 := hv.eq_of_src _ _
    rw [hi, comp_zero]
  change (P.projection 1).app E.obj = 𝟙 E.obj
  calc
    (P.projection 1).app E.obj = ∑ g : G, (P.projection g).app E.obj := by
      symm
      apply Finset.sum_eq_single 1
      · intro g _ hg
        exact hp g hg
      · simp
    _ = 𝟙 E.obj := P.total E.obj

/-- In the genuine gauged braiding, every actual transparent object has
actual neutral underlying object. -/
theorem transparent_homogeneous (E : A.Equivariant) :
    letI := B.equivariantBraidedCategory
    E ∈ mugerCenter → P.Homogeneous 1 E.obj := by
  letI := B.equivariantBraidedCategory
  intro hE
  apply B.homogeneous_of_regularUnit_monodromy E
  have hc := hE (regularUnit (A := A)) (Set.mem_univ _)
  change (B.equivariantBraiding E (regularUnit (A := A))).hom ≫
    (B.equivariantBraiding (regularUnit (A := A)) E).hom = 𝟙 _ at hc
  simpa only [WeakAction.Equivariant.comp_hom, equivariantBraiding_hom,
    WeakAction.Equivariant.id_hom] using congrArg WeakAction.Equivariant.Hom.hom hc

end Paper18.Category.CrossedBraidedGauging.CrossedBraiding
