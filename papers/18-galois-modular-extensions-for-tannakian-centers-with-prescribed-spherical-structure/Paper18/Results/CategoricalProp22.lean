import Paper18.Results.CategoricalLacabanne
import Paper18.Category.PivotalBalancingInvertible
import Paper18.Category.SemisimpleCoendBasic

/-! # The actual negative-boson exclusion in Proposition 2.2

The spherical boundary forces the actual slope to centralize its image.
When the ambient centralizer has precisely the two indicated simple objects,
the inverse-twist assertion of Lemma 2.1 excludes the negative-dimensional
boson, and the actual pivotal structure is spherical.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w v' u' w'
namespace Paper18.Category
attribute [local instance 2000] RightRigidCategory.rightDual

section Boundary
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton D κ)
  (F : C ⥤ D) [F.Additive] [F.Linear ℂ] [F.Monoidal] [F.Full] [F.Faithful]
  (JC : PivotalStructure C) (JD : PivotalStructure D)
  (hF : PreservesPivotal F JC JD) (hJC : JC.Spherical)

include S T hF hJC in
/-- A spherical pivotal boundary makes every actual slope component on its
image the identity; this includes nonsimple image objects. -/
lemma slope_on_spherical_image (X : C) : JD.slope.hom.app (F.obj X) = 𝟙 (F.obj X) := by
  have hs (i : ι) : JD.slope.hom.app (F.obj (S.simpleObject i)) =
      𝟙 (F.obj (S.simpleObject i)) := by
    letI := T.simple_map F (S.simpleObject i)
    rw [JD.slope_hom_app_simple T, JD.rightDim_dual]
    have hd : JD.leftDim (F.obj (S.simpleObject i)) = JD.rightDim (F.obj (S.simpleObject i)) :=
      congrArg (unitScalarEquiv (C := D)) (hF.spherical_on_image hJC _ (𝟙 _))
    rw [hd, div_self (JD.rightDim_ne_zero T _), one_smul]
  apply S.coend_map_hom_ext F X
  intro a
  have hn := JD.slope.hom.naturality (F.map (S.coendInclusion X a))
  change F.map (S.coendInclusion X a) ≫ JD.slope.hom.app (F.obj X) =
    JD.slope.hom.app (F.obj (S.simpleObject (S.label X a))) ≫
      F.map (S.coendInclusion X a) at hn
  exact hn.trans ((congrArg (fun k => k ≫ F.map (S.coendInclusion X a))
    (hs (S.label X a))).trans ((Category.id_comp _).trans (Category.comp_id _).symm))

include S T hF hJC in
/-- A slope representative belongs to the actual centralizer of the
spherical boundary. -/
lemma slope_representative_in_centralizer {t : D} (A : TensorInverse t)
    (hA : A.monodromyCharacter = JD.slope) : t ∈ centralizer (Set.range F.obj) := by
  intro Y hY
  obtain ⟨X,rfl⟩ := hY
  change (doubleBraiding t (F.obj X)).hom = 𝟙 (t ⊗ F.obj X)
  rw [← A.monodromyCharacter_spec, hA, slope_on_spherical_image S T F JC JD hF hJC X]
  exact whiskerLeft_id _ _

end Boundary

section Exclusion
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (J : PivotalStructure C) (hC : IsNondegenerate (C := C))

/-- An inverse of an object isomorphic to an actual order-two object is
isomorphic to that object. This uses the actual inverse isomorphisms. -/
def TensorInverse.inverseIsoOfSquare {t f : C} (A : TensorInverse t)
    (e : t ≅ f) (he : f ⊗ f ≅ 𝟙_ C) : A.inverse ≅ f :=
  (ρ_ A.inverse).symm ≪≫ (Iso.refl _ ⊗ᵢ he.symm) ≪≫
    (α_ A.inverse f f).symm ≪≫
      (((Iso.refl _ ⊗ᵢ e.symm) ≪≫ A.left) ⊗ᵢ Iso.refl f) ≪≫ λ_ f

include S hC in
/-- The complete negative-boson exclusion: actual centralizer support on
the unit and a negative-dimensional order-two boson forces sphericality.
The support assumption is an actual categorical centralizer property. -/
theorem spherical_of_negative_boson_centralizer
    (B : Set C) {f : C} (E : TensorInverse f) (he : f ⊗ f ≅ 𝟙_ C)
    (hf : (β_ f f).hom = 𝟙 (f ⊗ f)) (hdf : J.rightDim f = -1)
    (hboundary : ∀ X ∈ B, J.slope.hom.app X = 𝟙 X)
    (hcentralizer : ∀ t : C, Simple t → t ∈ centralizer B →
      Nonempty (t ≅ 𝟙_ C) ∨ Nonempty (t ≅ f)) : J.Spherical := by
  obtain ⟨t,A,hA⟩ := lacabanne_representative S J hC
  letI := A.simple S
  have hc : t ∈ centralizer B := by
    intro X hX
    change (doubleBraiding t X).hom = 𝟙 (t ⊗ X)
    rw [← A.monodromyCharacter_spec, hA, hboundary X hX]
    exact whiskerLeft_id _ _
  rcases hcentralizer t inferInstance hc with hu | hfu
  · obtain ⟨e⟩ := hu
    apply (J.slope_eq_refl_iff_spherical S).mp
    rw [← hA]
    exact A.monodromyCharacter_eq_refl_iff.mpr (by
      intro X _
      exact (centralizes_unit_left X).of_iso_left e)
  · obtain ⟨e⟩ := hfu
    have ht := lacabanne_inverse_twist_of_nonzeroGauss S J A hA
      (J.pivotalGaussSum_ne_zero S hC)
    let ef := A.inverseIsoOfSquare e he
    have hθf : (J.twistIso f).hom = 𝟙 f := by
      apply (cancel_epi ef.hom).mp
      exact (J.twist_naturality ef.hom).trans (by rw [ht]; simp)
    have hneg := E.twistIso_eq_neg_id S J hf hdf
    have heq : (1 : ℂ) • 𝟙 f = (-1 : ℂ) • 𝟙 f :=
      (one_smul ℂ (𝟙 f)).trans (hθf.symm.trans hneg)
    letI := E.simple S
    have hz : (1 : ℂ) = -1 := smul_left_injective ℂ (CategoryTheory.id_nonzero f) heq
    norm_num at hz

end Exclusion
end Paper18.Category
