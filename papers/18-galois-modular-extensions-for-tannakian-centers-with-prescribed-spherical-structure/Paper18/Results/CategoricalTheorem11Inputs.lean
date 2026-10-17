import Paper18.External.JohnsonFreyd23
import Paper18.Category.SphericalizationC2Negative
import Paper18.Category.FixedBoundaryMinimalExistenceENO

/-! # Precise external existence inputs for Theorem 1.1

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

/-- Choose the actual first nonspherical extension supplied by the exact
external JF theorem. No pivotal structure is included in this choice. -/
def initialExtension (jf : Paper18.External.JohnsonFreyd23.{v,u,w}) :
    GaloisBraidedExtension.{v,u,max u v,max u (v+1),max (max u v) w} C :=
  Classical.choice (jf S T)

/-- The precise external ENO realization input needed in the proof: its
source is the actual sphericalization of the chosen first JF extension,
and its C₂ action is the actual Tannakian de-equivariant action. -/
def InitialObstructionInput (jf : Paper18.External.JohnsonFreyd23.{v,u,w}) : Prop :=
  FixedBoundary.MinimalExistence.TannakianObstructionInput.{
    max u v,max u (v+1),max (max u v) w,
    max u v,max u (v+1),max (max u v) w}
    (Sphericalized.skeleton (initialExtension S T jf).skeleton)
    (Sphericalized.tannakianCenter (initialExtension S T jf).nondegenerate)

end Paper18.Category.CategoricalTheorem11
