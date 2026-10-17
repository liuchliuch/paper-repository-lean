import Paper18.Category.SphericalizationKernelTannakian
import Paper18.Category.SphericalizationNegative
import Paper18.Category.TannakianC2GeneratorDecomposition

/-! # The canonical C₂ generator in actual sphericalization

The distinguished sign representation of the actual transparent center is
identified with the constructed negative sphericalization object. This
supplies the prescribed negative dimension required by Proposition 2.2.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u w
namespace Paper18.Category.Sphericalized
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasFiniteBiproducts C] [HasKernels C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

/-- The actual sign generator of any C₂ presentation of the transparent
center is the actual negative sphericalization object. -/
def c2GeneratorIsoNegative (T : TannakianCenter (Sphericalized C) RepresentationZ2.H) :
    T.c2Generator ≅ negativeGenerator (C := C) := by
  have hZ : negativeGenerator (C := C) ∈ mugerCenter :=
    fun Y _ => negativeGenerator_centralizes Y
  have h := (T.c2Generator_simple_support (negativeGenerator (C := C)) hZ).resolve_left
    (negativeGenerator_not_iso_unit S)
  exact (Classical.choice h).symm

include S

/-- The sign generator has exactly the prescribed negative pivotal dimension;
this assertion requires no pivotal structure on the original category. -/
theorem c2Generator_rightDim (T : TannakianCenter (Sphericalized C) RepresentationZ2.H) :
    (pivotalStructure (C := C)).rightDim T.c2Generator = -1 := by
  rw [(pivotalStructure (C := C)).rightDim_iso (c2GeneratorIsoNegative S T)]
  exact negativeGenerator_rightDim S

/-- The canonical actual presentation of the center has the same negative
sign generator whenever the original category is nondegenerate. -/
theorem tannakianCenter_c2Generator_rightDim (hC : IsNondegenerate (C := C)) :
    (pivotalStructure (C := C)).rightDim (tannakianCenter hC).c2Generator = -1 :=
  c2Generator_rightDim S (tannakianCenter hC)

end Paper18.Category.Sphericalized
