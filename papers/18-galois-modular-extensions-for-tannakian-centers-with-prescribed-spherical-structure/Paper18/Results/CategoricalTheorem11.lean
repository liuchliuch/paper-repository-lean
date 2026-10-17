import Paper18.Results.CategoricalTheorem11Preliminary
import Paper18.Results.CategoricalTheorem11Inputs

/-! # Theorem 1.1 with its precise external existence inputs

The two uses of Johnson--Freyd Proposition 2.3 supply actual nonspherical
braided extensions with integral centralizers. The ENO obstruction-realization
input is applied only to the actual sphericalization of the first extension.
All prescribed spherical structures, sign-character branches, condensation,
and final integral-centralizer conclusions are constructed by this project.

The same essentially small target sizes are used for both applications of
JF Proposition 2.3. Consequently the output has exactly the canonical universe
bounds of the original challenge.
-/
noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category.CategoricalTheorem11
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [RightRigidCategory C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {G : Type} [Group G] (T : TannakianCenter C G)

/-- Theorem 1.1: every prescribed spherical structure on an actual complex
braided fusion category with Tannakian center admits an actual modular
extension with integral centralizer. The published nonspherical JF theorem
and the precise ENO obstruction-realization theorem are explicit hypotheses;
the spherical extension and both own-paper cases are proved internally. -/
theorem exists_modularExtension (J : PivotalStructure C) (hJ : J.Spherical)
    (jf : Paper18.External.JohnsonFreyd23.{v,u,w})
    (jfKernel : Paper18.External.JohnsonFreyd23At.{
      max u v,max u (v+1),max (max u v) w,
      max u v,max u (v+1),max (max u v) w})
    (hENO : InitialObstructionInput S T jf) :
    Nonempty (ModularExtension.{v,u,max u v,max u (v+1),max (max u v) w} J) := by
  let E0 := initialExtension S T jf
  obtain ⟨E⟩ := FixedBoundary.MinimalExistence.minimalExtension_exists
    (Sphericalized.skeleton E0.skeleton)
    (Sphericalized.tannakianCenter E0.nondegenerate) hENO
  exact fromInitialMinimal.{v,u,w,max u v,max u (v+1),max (max u v) w,
    max u v,max u (v+1),max (max u v) w} S J hJ T E0 E jfKernel

end Paper18.Category.CategoricalTheorem11
