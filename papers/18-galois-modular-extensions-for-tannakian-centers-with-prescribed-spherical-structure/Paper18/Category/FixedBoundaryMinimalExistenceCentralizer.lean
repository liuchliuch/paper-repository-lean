import Paper18.Category.FixedBoundaryMinimalExistenceSourceImage
import Paper18.Category.CrossedBraidedGaugingCentralizerIntegral

/-! # Integrality of the reconstructed original-source centralizer

The actual source image is identified with the actual neutral equivariant
objects before the crossed-gauging centralizer theorem is applied.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits Functor.LaxMonoidal
open Paper18.Category.CrossedBraidedGauging
universe v₀ u₀ w₀ v₁ u₁ w₁ v₂ u₂ w₂
namespace Paper18.Category.FixedBoundary.MinimalExistence
variable {C : Type u₀} [Category.{v₀} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  {ι : Type w₀} [Fintype ι] (SC : FiniteSemisimpleSkeleton C ι)
  {D : Type u₁} [Category.{v₁} D] [Preadditive D] [Linear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [RightRigidCategory D] [Simple (𝟙_ D)]
  {κ : Type w₁} [Fintype κ] (SD : FiniteSemisimpleSkeleton D κ)
  {A : WeakAction C2 C} {H : WeakAction C2 D}
  [∀ g : C2, (A.ρ g).Monoidal] [A.IsMonoidal] [A.IsBraided]
  [∀ g : C2, (H.ρ g).Monoidal] [H.IsMonoidal]
  [∀ g : C2, (A.ρ g).Additive] [∀ g : C2, (A.ρ g).Linear ℂ]
  [∀ g : C2, (H.ρ g).Additive] [∀ g : C2, (H.ρ g).Linear ℂ]
  {P : Grading C2 D} {Q : GradedAction P H} (B : CrossedBraiding P H Q)
  (F : A.Intertwiner H) [F.functor.Monoidal] [F.IsMonoidal]
  [F.functor.Additive] [F.functor.Linear ℂ] [F.functor.Full] [F.functor.Faithful]
  (hdeg : ∀ X : C, P.Homogeneous 1 (F.functor.obj X))
  (hcover : ∀ Y : D, P.Homogeneous 1 Y → ∃ X : C, Nonempty (F.functor.obj X ≅ Y))

variable {R : Type u₂} [Category.{v₂} R] [Preadditive R] [Linear ℂ R]
  [HasKernels R] [HasFiniteBiproducts R]
  [∀ X Y : R, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory R] [BraidedCategory R] [MonoidalPreadditive R] [MonoidalLinear ℂ R]
  [RightRigidCategory R] [Simple (𝟙_ R)]
  {ν : Type w₂} [Fintype ν] (SR : FiniteSemisimpleSkeleton R ν)
  (E : R ⥤ A.Equivariant) [E.IsEquivalence] [E.Additive] [E.Linear ℂ] [E.Braided]

include SC SD SR hdeg hcover E in
/-- The actual original-source centralizer is precisely the actual
neutral equivariant centralizer. Isomorphic representatives do not affect
centralization. -/
theorem sourceEmbedding_centralizer (hf : P.Faithful) :
    letI := B.equivariantBraidedCategory
    centralizer (Set.range (sourceEmbedding F E).obj) =
      centralizer (neutralEquivariantObjects P H) := by
  letI := B.equivariantBraidedCategory
  rw [← RelativeTensor.centralizer_essImage (sourceEmbedding F E)]
  congr 1
  ext Y
  rw [sourceEmbedding_essImage (Q := Q) SC SD F hdeg hcover SR E hf]
  exact equivariantGrading_homogeneous Q 1 Y

include SC SD SR hdeg hcover E in
/-- The original-source centralizer is intrinsically integral, as a
consequence of actual source reconstruction and actual neutral
nondegeneracy. -/
theorem sourceEmbeddingCentralizerIntegral (hf : P.Faithful)
    (hβ : ∀ X Y : C, μ F.functor X Y ≫ F.functor.map (β_ X Y).hom =
      (B.neutralIso (F.functor.obj X) (hdeg X) (F.functor.obj Y)).hom ≫ μ F.functor Y X)
    (hC : IsNondegenerate (C := C)) :
    letI := B.equivariantBraidedCategory
    (gaugingSkeleton SD).CentralizerIntegral (Set.range (sourceEmbedding F E).obj) := by
  letI := B.equivariantBraidedCategory
  apply (gaugingSkeleton SD).centralizerIntegral_iff _ |>.mpr
  intro j hj
  have hc := sourceEmbedding_centralizer SC SD B F hdeg hcover SR E hf
  rw [hc] at hj
  exact B.centralizer_fpdim_integer SD
    (neutral_nondegenerate B F.functor hdeg hβ hcover hC) _ hj

end Paper18.Category.FixedBoundary.MinimalExistence
