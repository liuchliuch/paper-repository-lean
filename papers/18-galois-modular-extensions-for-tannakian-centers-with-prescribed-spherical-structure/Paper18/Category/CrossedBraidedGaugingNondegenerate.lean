import Paper18.Category.CrossedBraidedGaugingTransparentUnitHom
import Paper18.Category.CrossedBraidedGaugingFusion

/-! # Genuine nondegeneracy of faithful crossed gauging

The hypotheses concern only the actual faithful grading and actual
nondegenerate neutral category. Transparency, neutral support, unit-sum
decomposition, and triviality of the equivariant structure are derived.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w t
namespace Paper18.Category.CrossedBraidedGauging.CrossedBraiding
variable {G : Type w} [Group G] [Fintype G]
  {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {P : Grading G C} {A : WeakAction G C}
  [∀ g : G, (A.ρ g).Monoidal] [A.IsMonoidal]
  [∀ g : G, (A.ρ g).Additive] [∀ g : G, (A.ρ g).Linear ℂ]
  {Q : GradedAction P A} (B : CrossedBraiding P A Q)
  {ι : Type t} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

/-- Every actual raw unit map to a transparent object lifts to an actual
equivariant map, by the proved faithful-degree detection. -/
def transparentUnitHom (hF : P.Faithful) (E : A.Equivariant)
    (hE : letI := B.equivariantBraidedCategory; E ∈ mugerCenter)
    (f : (𝟙_ C) ⟶ E.obj) : (𝟙_ A.Equivariant) ⟶ E where
  hom := f
  comm g := by
    change (A.ρ g).map f ≫ (E.structureIso g).hom = Functor.OplaxMonoidal.η (A.ρ g) ≫ f
    exact B.unitHom_equivariant S hF E hE f g

include S in
/-- An actual faithful finite crossed braided fusion category with actual
nondegenerate neutral component has actual nondegenerate equivariantization. -/
theorem equivariant_nondegenerate (hF : P.Faithful)
    (hN : letI := B.neutralBraidedCategory; IsNondegenerate (C := Neutral P)) :
    letI := B.equivariantBraidedCategory
    IsNondegenerate (C := A.Equivariant) := by
  letI := B.equivariantBraidedCategory
  intro E hE
  obtain ⟨n, ⟨e⟩⟩ := B.transparent_underlying_unitSum hN E hE
  let q : (⨁ fun _ : Fin n => 𝟙_ A.Equivariant) ⟶ E :=
    biproduct.desc (fun j : Fin n => B.transparentUnitHom S hF E hE
      (biproduct.ι (fun _ : Fin n => 𝟙_ C) j ≫ e.inv))
  have hq : A.forget.map q =
      (A.forget.mapBiproduct (fun _ : Fin n => 𝟙_ A.Equivariant)).hom ≫ e.inv := by
    apply map_biproduct_hom_ext A.forget (fun _ : Fin n => 𝟙_ A.Equivariant)
    intro j
    rw [← A.forget.map_comp, map_biproduct_ι_assoc]
    dsimp only [q]
    rw [biproduct.ι_desc]
    rfl
  letI : IsIso (A.forget.map q) := by
    rw [hq]
    infer_instance
  letI : IsIso q := isIso_of_reflects_iso q A.forget
  exact ⟨n, ⟨(asIso q).symm⟩⟩

end Paper18.Category.CrossedBraidedGauging.CrossedBraiding
