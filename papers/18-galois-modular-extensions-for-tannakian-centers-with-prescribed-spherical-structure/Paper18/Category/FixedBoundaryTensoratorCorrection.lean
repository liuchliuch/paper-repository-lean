import Paper18.Category.FixedBoundaryTensoratorRigid

/-! # Actual H² correction in a possibly nonbraided ambient category

This is the de-equivariantized application: genuine left and right mixed
compatibilities imply actual scalar exhaustivity and then an actual
monoidal comparison fixing the prescribed neutral comparison.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category.FixedBoundary
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [HasKernels C] [HasFiniteBiproducts C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (χ : 𝟭 C ≅ 𝟭 C) [NatTrans.IsMonoidal χ.hom]
  (hχ : ∀ X : C, χ.hom.app X ≫ χ.hom.app X = 𝟙 X)
  (F : C ⥤ C) [F.Monoidal]
  (a : SignKernel.inclusion χ ⋙ F ≅ SignKernel.inclusion χ)
  [NatTrans.IsMonoidal a.hom]
  (e : F ≅ 𝟭 C)
  (he : ∀ X : SignKernel.Positive χ, e.hom.app X.obj = a.hom.app X)

include he in
/-- The specified monoidal neutral comparison forces the actual unit law. -/
lemma comparison_unit_of_positive :
    Functor.LaxMonoidal.ε F ≫ e.hom.app (𝟙_ C) = 𝟙 (𝟙_ C) := by
  have hh := NatTrans.IsMonoidal.unit (τ := a.hom)
  change (Functor.LaxMonoidal.ε F ≫ F.map (𝟙 _)) ≫
      a.hom.app (𝟙_ (SignKernel.Positive χ)) = 𝟙 _ at hh
  change Functor.LaxMonoidal.ε F ≫ e.hom.app (𝟙_ (SignKernel.Positive χ)).obj = _
  rw [he]
  simpa only [F.map_id, Category.comp_id] using hh

variable
  (h0l : ∀ {g : ZMod 2} {X Y : C}, Homogeneous χ 0 X → Homogeneous χ g Y →
    tensoratorDefect F e X Y = 𝟙 _)
  (h0r : ∀ {g : ZMod 2} {X Y : C}, Homogeneous χ g X → Homogeneous χ 0 Y →
    tensoratorDefect F e X Y = 𝟙 _)
  (j : ι) (hj : Homogeneous χ 1 (S.simpleObject j))

include S hχ he h0l h0r hj in
/-- Actual mixed compatibility constructs an actual normalized cochain
whose actual gauge correction is monoidal and retains the prescribed
neutral comparison. The cochain is derived, rather than supplied. -/
theorem exists_monoidal_gauge_of_mixed :
    ∃ μ : ZMod 2 → ℂˣ, μ 0 = 1 ∧
      NatTrans.IsMonoidal (correctedIso F e χ hχ μ).hom ∧
        ∀ X : SignKernel.Positive χ,
          (correctedIso F e χ hχ μ).hom.app X.obj = a.hom.app X := by
  obtain ⟨lam, hd⟩ := exists_tensorator_cocycle_of_mixed F e χ h0l h0r S j hj
  obtain ⟨μ, hμ0, hμ⟩ := Paper18.lemmaA_1_cohomology lam
  refine ⟨μ, hμ0, correctedIso_monoidal F e χ hχ S lam μ hμ0 hμ
    (comparison_unit_of_positive χ F a e he) hd, ?_⟩
  intro X
  change e.hom.app X.obj ≫ (gaugeNatIso χ hχ (μ 1)).hom.app X.obj = a.hom.app X
  rw [gaugeNatIso_homogeneous χ hχ μ hμ0 X.property, hμ0]
  simpa using he X

include S hχ he h0l h0r hj in
/-- Genuine mixed compatibility produces an actual monoidal comparison
with the prescribed neutral component. Scalar coordinates and the C₂
cocycle are derived internally; no ambient braiding is required. -/
theorem exists_monoidal_comparison_of_mixed :
    ∃ β : F ≅ 𝟭 C, NatTrans.IsMonoidal β.hom ∧
      ∀ X : SignKernel.Positive χ, β.hom.app X.obj = a.hom.app X := by
  obtain ⟨μ, _, hm, hb⟩ := exists_monoidal_gauge_of_mixed S χ hχ F a e he h0l h0r j hj
  exact ⟨correctedIso F e χ hχ μ, hm, hb⟩

end Paper18.Category.FixedBoundary
