import Paper18.Category.PointedRepEquivalenceTotal
import Paper18.Category.PointedTensorCharacters

/-! # Actual tensor products of homogeneous lines

The comparison with the total vector space is used only for objects and
linear Hom spaces. Its monoidal coherence is not used after an associator twist.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
namespace Paper18.Category.QuasiFusion
variable {A : Type} [Fintype A] [AddGroup A]

/-- The total vector space of a homogeneous line is the actual complex line. -/
def homogeneousTotalIso (a : A) :
    PointedVec.totalFunctor.obj (PointedVec.simpleObject A a) ≅ FGModuleCat.of ℂ ℂ where
  hom := biproduct.π (PointedVec.simpleObject A a) a ≫ (PointedVec.simpleFiberIso A a).hom
  inv := (PointedVec.simpleFiberIso A a).inv ≫ biproduct.ι (PointedVec.simpleObject A a) a
  hom_inv_id := by
    apply biproduct.hom_ext'
    intro b
    by_cases hb : b = a
    · subst b
      simp
      exact (comp_id _).symm
    · exact (PointedVec.simpleFiber_isZero A a b hb).eq_of_src _ _
  inv_hom_id := by simp

/-- Tensoring two homogeneous lines has a one-dimensional total vector space. -/
def homogeneousTensorTotalIso (a b : A) :
    PointedVec.totalFunctor.obj
      (PointedVec.simpleObject A a ⊗ PointedVec.simpleObject A b) ≅
        FGModuleCat.of ℂ ℂ :=
  (PointedVec.totalTensorIso _ _).symm ≪≫
    (homogeneousTotalIso a ⊗ᵢ homogeneousTotalIso b) ≪≫ λ_ (FGModuleCat.of ℂ ℂ)

/-- The actual convolution tensor of two homogeneous lines is simple. -/
theorem homogeneousTensor_simple (a b : A) :
    Simple (PointedVec.simpleObject A a ⊗ PointedVec.simpleObject A b) := by
  let X := PointedVec.simpleObject A a ⊗ PointedVec.simpleObject A b
  let F := PointedVec.totalFunctor (A := A)
  letI : Simple (F.obj X) := by
    letI := PointedVec.simple_complex_line
    exact Simple.of_iso (homogeneousTensorTotalIso a b)
  apply (PointedVec.skeleton A).simple_of_finrank_end_eq_one X
  have hle : Module.finrank ℂ (X ⟶ X) ≤ 1 := by
    have h := LinearMap.finrank_le_finrank_of_injective
      (f := F.mapLinearMap ℂ (X := X) (Y := X)) F.map_injective
    simpa only [CategoryTheory.finrank_endomorphism_simple_eq_one ℂ (F.obj X)] using h
  have hid : (𝟙 X : X ⟶ X) ≠ 0 := by
    intro h
    obtain ⟨f, hf⟩ := PointedVec.simple_tensor_nonzero_hom a b
    apply hf
    calc
      f = f ≫ 𝟙 X := (comp_id f).symm
      _ = 0 := by rw [h, comp_zero]
  have hpos : 0 < Module.finrank ℂ (X ⟶ X) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨𝟙 X, hid⟩
  omega

/-- The product rule is witnessed by an actual graded-vector-space isomorphism. -/
def homogeneousTensorIso (a b : A) :
    PointedVec.simpleObject A a ⊗ PointedVec.simpleObject A b ≅
      PointedVec.simpleObject A (a + b) := by
  letI := homogeneousTensor_simple a b
  letI := PointedVec.simple_simpleObject (A := A) (a + b)
  let f := Classical.choose (PointedVec.simple_tensor_nonzero_hom a b)
  have hf : f ≠ 0 := Classical.choose_spec (PointedVec.simple_tensor_nonzero_hom a b)
  letI := CategoryTheory.isIso_of_hom_simple hf
  exact (asIso f).symm

end Paper18.Category.QuasiFusion
