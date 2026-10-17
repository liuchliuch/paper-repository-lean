import Paper18.Category.FixedBoundaryScalarGauge

/-!
# Boundary-retaining trivialization from an actual scalar tensorator defect

This theorem constructs a monoidal natural isomorphism on the original
category from an ordinary natural identification and a verified scalar
formula for its tensorator defect. Its boundary is exactly the prescribed
one. The ordinary identification and scalar formula are hypotheses here;
no claim of categorical classification or Lemma A.1 existence is made.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w v' u'
namespace Paper18.Category

section Unit
variable {A : Type u'} [Category.{v'} A] [Preadditive A] [Linear ℂ A]
  [MonoidalCategory A] [BraidedCategory A]
  {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [BraidedCategory C]
  (i : A ⥤ C) [i.Monoidal] (P : BoundaryAutoequivalence i)
  (e : P.functor ≅ 𝟭 C)

/-- Agreement with the specified monoidal boundary already forces the
unit equation for an ordinary natural identification. -/
theorem BoundaryAutoequivalence.unit_of_boundary_compatibility
    (he : ∀ X : A, e.hom.app (i.obj X) = P.boundary.hom.app X) :
    Functor.LaxMonoidal.ε P.functor ≫ e.hom.app (𝟙_ C) = 𝟙 (𝟙_ C) := by
  apply (cancel_mono (Functor.LaxMonoidal.ε i)).mp
  have hn := e.hom.naturality (Functor.LaxMonoidal.ε i)
  change P.functor.map (Functor.LaxMonoidal.ε i) ≫ e.hom.app (i.obj (𝟙_ A)) =
    e.hom.app (𝟙_ C) ≫ Functor.LaxMonoidal.ε i at hn
  calc
    _ = Functor.LaxMonoidal.ε P.functor ≫
        P.functor.map (Functor.LaxMonoidal.ε i) ≫ e.hom.app (i.obj (𝟙_ A)) := by
      rw [Category.assoc, hn]
    _ = Functor.LaxMonoidal.ε i := by
      rw [he]
      simpa only [Functor.LaxMonoidal.comp_ε, Category.assoc] using
        (NatTrans.IsMonoidal.unit (τ := P.boundary.hom))
    _ = _ := (Category.id_comp _).symm

end Unit

section Trivialization
variable {A : Type u'} [Category.{v'} A] [Preadditive A] [Linear ℂ A]
  [MonoidalCategory A] [BraidedCategory A]
  {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [BraidedCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (i : A ⥤ C) [i.Monoidal] (P : BoundaryAutoequivalence i)
  (χ : 𝟭 C ≅ 𝟭 C) [NatTrans.IsMonoidal χ.hom]
  (hχ : ∀ X : C, χ.hom.app X ≫ χ.hom.app X = 𝟙 X)

include S hχ in
/-- The scalar H² calculation produces an actual boundary-retaining
monoidal trivialization once scalar coordinates of the actual tensorator
have been proved. In particular the conclusion is a `BoundaryIso`, not a
cochain-level equivalence relation. -/
theorem BoundaryAutoequivalence.trivializable_of_scalar_tensorator_defect
    (e : P.functor ≅ 𝟭 C)
    (he : ∀ X : A, e.hom.app (i.obj X) = P.boundary.hom.app X)
    (hi : ∀ X : A, FixedBoundary.Homogeneous χ 0 (i.obj X))
    (lam : Paper18.Z2Cocycle)
    (hd : ∀ (g h : ZMod 2) (X Y : C),
      FixedBoundary.Homogeneous χ g X → FixedBoundary.Homogeneous χ h Y →
      FixedBoundary.tensoratorDefect P.functor e X Y =
        (lam.toFun g h : ℂ) • 𝟙 (X ⊗ Y)) : P.Trivializable := by
  obtain ⟨μ, hμ0, hμ⟩ := Paper18.lemmaA_1_cohomology lam
  let β := FixedBoundary.correctedIso P.functor e χ hχ μ
  letI : NatTrans.IsMonoidal β.hom := FixedBoundary.correctedIso_monoidal
    P.functor e χ hχ S lam μ hμ0 hμ
    (P.unit_of_boundary_compatibility i e he) hd
  refine ⟨{ iso := β, boundary := ?_ }⟩
  intro X
  change (e.hom.app (i.obj X) ≫
    (FixedBoundary.gaugeNatIso χ hχ (μ 1)).hom.app (i.obj X)) ≫ 𝟙 _ = _
  rw [FixedBoundary.gaugeNatIso_homogeneous χ hχ μ hμ0 (hi X), hμ0]
  simpa using he X

end Trivialization
end Paper18.Category
