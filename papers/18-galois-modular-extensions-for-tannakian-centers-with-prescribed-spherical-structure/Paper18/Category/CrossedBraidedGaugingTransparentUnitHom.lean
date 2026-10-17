import Paper18.Category.CrossedBraidedGaugingTransparentUnderlying
import Paper18.Category.GraphPicardContraction

/-! # Faithful crossed degrees force trivial equivariance of unit maps -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits Functor.LaxMonoidal Functor.OplaxMonoidal
universe v u w t
namespace Paper18.Category.CrossedBraidedGauging.CrossedBraiding
variable {G : Type w} [Group G] [Fintype G]
  {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasFiniteBiproducts C] [HasKernels C]
  {P : Grading G C} {A : WeakAction G C}
  [∀ g : G, (A.ρ g).Monoidal] [A.IsMonoidal]
  [∀ g : G, (A.ρ g).Additive]
  {Q : GradedAction P A} (B : CrossedBraiding P A Q)

/-- Actual monodromy reads the g-translate of a raw map out of the unit. -/
theorem unitHom_monodromy (g : G) (Y : C) (hY : P.Homogeneous g Y)
    (E : A.Equivariant) (hX : P.Homogeneous 1 E.obj) (f : (𝟙_ C) ⟶ E.obj) :
    (Y ◁ f) ≫ (B.blockIso g Y hY E).hom ≫ (B.neutralIso E.obj hX Y).hom =
      Y ◁ (ε (A.ρ g) ≫ (A.ρ g).map f ≫ (E.structureIso g).hom) := by
  let ff := ε (A.ρ g) ≫ (A.ρ g).map f ≫ (E.structureIso g).hom
  have hn := B.neutralIso_naturality_left P.homogeneous_unit hX ff Y
  simp only [ff, comp_whiskerRight, Category.assoc] at hn
  rw [blockIso_hom]
  simp only [Category.assoc]
  rw [← Category.assoc (Y ◁ f), B.naturality_right, B.unit_right]
  simp only [Category.assoc]
  rw [hn, B.neutralIso_unit_left]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]

/-- A transparent actual equivariant object has trivial actual monodromy
with every homogeneous raw object, using genuine induction dominance. -/
theorem homogeneous_monodromy_of_transparent (E : A.Equivariant) :
    letI := B.equivariantBraidedCategory
    ∀ hE : E ∈ mugerCenter, ∀ (g : G) (Y : C) (hY : P.Homogeneous g Y),
      (B.blockIso g Y hY E).hom ≫
        (B.neutralIso E.obj (B.transparent_homogeneous E hE) Y).hom = 𝟙 (Y ⊗ E.obj) := by
  letI := B.equivariantBraidedCategory
  intro hE g Y hY
  let hX := B.transparent_homogeneous E hE
  let r := A.inductionRetract Y
  let sm : SplitMono (r.i ▷ E.obj) :=
    ⟨r.r ▷ E.obj, by rw [← comp_whiskerRight, r.retract, id_whiskerRight]⟩
  letI : Mono (r.i ▷ E.obj) := sm.mono
  apply (cancel_mono (r.i ▷ E.obj)).mp
  simp only [Category.assoc, Category.id_comp]
  rw [← B.neutralIso_naturality_right E.obj hX r.i]
  rw [← B.halfSwapIso_homogeneous g Y hY]
  erw [B.neutralIso_eq_block E.obj hX (A.induction Y),
    ← B.halfSwapIso_homogeneous 1 E.obj hX]
  rw [← Category.assoc, ← B.halfSwapIso_naturality_left r.i E, Category.assoc]
  have hc := (hE (A.induction Y) (Set.mem_univ _)).symm
  change (B.equivariantBraiding (A.induction Y) E).hom ≫
    (B.equivariantBraiding E (A.induction Y)).hom = 𝟙 _ at hc
  have hu := congrArg WeakAction.Equivariant.Hom.hom hc
  simp only [WeakAction.Equivariant.comp_hom, equivariantBraiding_hom,
    WeakAction.Equivariant.id_hom] at hu
  erw [hu, Category.comp_id]

section Fusion
variable [Linear ℂ C] [MonoidalLinear ℂ C] [RightRigidCategory C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type t} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

include S in
/-- Faithfulness of the genuine grading forces every raw map from the
unit into a transparent equivariant object to be equivariant. -/
theorem unitHom_equivariant (hF : P.Faithful) (E : A.Equivariant) :
    letI := B.equivariantBraidedCategory
    ∀ hE : E ∈ mugerCenter, ∀ (f : (𝟙_ C) ⟶ E.obj) (g : G),
      (A.ρ g).map f ≫ (E.structureIso g).hom = η (A.ρ g) ≫ f := by
  letI := B.equivariantBraidedCategory
  intro hE f g
  obtain ⟨Y, hY, hnY⟩ := hF g
  letI : (tensorLeft Y).Faithful := GraphPicard.tensorLeftFaithfulOfNonzero S Y
    (fun hz => hnY ((IsZero.iff_id_eq_zero Y).mpr hz))
  have hm := B.homogeneous_monodromy_of_transparent E hE g Y hY
  have he := congrArg (fun k => (Y ◁ f) ≫ k) hm
  dsimp only at he
  rw [B.unitHom_monodromy g Y hY E (B.transparent_homogeneous E hE) f] at he
  erw [Category.comp_id] at he
  have hf : ε (A.ρ g) ≫ (A.ρ g).map f ≫ (E.structureIso g).hom = f :=
    (tensorLeft Y).map_injective he
  apply (cancel_epi (ε (A.ρ g))).mp
  simpa only [Category.assoc, Functor.Monoidal.ε_η_assoc] using hf

end Fusion
end Paper18.Category.CrossedBraidedGauging.CrossedBraiding
