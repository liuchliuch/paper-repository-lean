import Paper18.Category.QuasiFusionRigid
import Paper18.Category.QuasiFusionSimpleTensor
import Paper18.Category.InvertibleObjects

/-! # Actual fusion and FP dimensions of twisted graded vector spaces -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace Paper18.Category.QuasiFusion
variable {A : Type} [Fintype A] [AddGroup A]
variable (r : A → A → A → ℂˣ)
  (hr : ∀ a b c d, r b c d * r a (b + c) d * r a b c =
    r (a + b) c d * r a b (c + d)) (h₀ : ∀ a c, r a 0 c = 1)
  (hinv : ∀ a, r (-a) a (-a) * r a (-a) a = 1)

def scalarSimpleUnit :
    letI := scalarMonoidalCategory r hr h₀
    Simple (𝟙_ (PointedVec A)) := by
  letI := scalarMonoidalCategory r hr h₀
  change Simple (PointedVec.simpleObject A 0)
  exact PointedVec.simple_simpleObject 0

/-- The inverse degree supplies actual two-sided tensor inverse data,
independently of the scalar associator. -/
def scalarHomogeneousTensorInverse (a : A) :
    letI := scalarMonoidalCategory r hr h₀
    TensorInverse (PointedVec.simpleObject A a) := by
  letI := scalarMonoidalCategory r hr h₀
  exact
    { inverse := PointedVec.simpleObject A (-a)
      left := homogeneousTensorIso (-a) a ≪≫
        eqToIso (congrArg (PointedVec.simpleObject A) (neg_add_cancel a)) ≪≫
        (PointedVec.unitSimpleIso A).symm
      right := homogeneousTensorIso a (-a) ≪≫
        eqToIso (congrArg (PointedVec.simpleObject A) (add_neg_cancel a)) ≪≫
        (PointedVec.unitSimpleIso A).symm }

/-- The actual twisted convolution category has the actual homogeneous-line
finite semisimple skeleton and derived fusion rules. -/
def scalarFusionBasis : Paper18.FusionBasis A := by
  letI := scalarMonoidalCategory r hr h₀
  letI := scalarMonoidalPreadditive r hr h₀
  letI := scalarMonoidalLinear r hr h₀
  letI := scalarRightRigid r hr h₀ hinv
  letI := scalarSimpleUnit r hr h₀
  exact (PointedVec.skeleton A).fusionBasis

/-- Each actual simple homogeneous line has FP dimension one. -/
theorem scalar_fpdim_homogeneous (a : A) :
    letI := scalarMonoidalCategory r hr h₀
    letI := scalarMonoidalPreadditive r hr h₀
    letI := scalarMonoidalLinear r hr h₀
    letI := scalarRightRigid r hr h₀ hinv
    letI := scalarSimpleUnit r hr h₀
    (PointedVec.skeleton A).fpdim (PointedVec.simpleObject A a) = 1 := by
  letI := scalarMonoidalCategory r hr h₀
  letI := scalarMonoidalPreadditive r hr h₀
  letI := scalarMonoidalLinear r hr h₀
  letI := scalarRightRigid r hr h₀ hinv
  letI := scalarSimpleUnit r hr h₀
  exact (PointedVec.skeleton A).fpdim_eq_one_of_tensorInvertible
    ⟨scalarHomogeneousTensorInverse r hr h₀ a⟩

@[simp] theorem scalarFusionBasis_fpdim (a : A) :
    (scalarFusionBasis r hr h₀ hinv).fpdim a = 1 := by
  letI := scalarMonoidalCategory r hr h₀
  letI := scalarMonoidalPreadditive r hr h₀
  letI := scalarMonoidalLinear r hr h₀
  letI := scalarRightRigid r hr h₀ hinv
  letI := scalarSimpleUnit r hr h₀
  have h := scalar_fpdim_homogeneous r hr h₀ hinv a
  change (PointedVec.skeleton A).fpdim ((PointedVec.skeleton A).simpleObject a) = 1 at h
  rw [FiniteSemisimpleSkeleton.fpdim_simple] at h
  exact h

/-- Integrality is proved for every actual categorical simple object. -/
theorem scalar_integral :
    letI := scalarMonoidalCategory r hr h₀
    letI := scalarMonoidalPreadditive r hr h₀
    letI := scalarMonoidalLinear r hr h₀
    letI := scalarRightRigid r hr h₀ hinv
    letI := scalarSimpleUnit r hr h₀
    (PointedVec.skeleton A).Integral := by
  letI := scalarMonoidalCategory r hr h₀
  letI := scalarMonoidalPreadditive r hr h₀
  letI := scalarMonoidalLinear r hr h₀
  letI := scalarRightRigid r hr h₀ hinv
  letI := scalarSimpleUnit r hr h₀
  apply (PointedVec.skeleton A).integral_iff_basis.mpr
  intro a
  exact ⟨1, by simpa only [Int.cast_one] using scalarFusionBasis_fpdim r hr h₀ hinv a⟩

/-- The actual total FP dimension is the cardinality of the grading group. -/
theorem scalar_totalFPdim :
    (scalarFusionBasis r hr h₀ hinv).totalFPdim = Fintype.card A := by
  simp [Paper18.FusionBasis.totalFPdim]

end Paper18.Category.QuasiFusion
