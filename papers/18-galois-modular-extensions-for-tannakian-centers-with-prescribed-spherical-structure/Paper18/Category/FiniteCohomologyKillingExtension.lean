import Paper18.Category.FiniteCohomologyKillingUniversal
import Mathlib.GroupTheory.GroupExtension.Defs

/-! # The actual finite universal cocycle extension -/
noncomputable section
universe u v
namespace Paper18.Category.FiniteCohomologyKilling
open Classical
variable (G : Type u) [Group G] (R : Type v) [CommRing R]

/-- The actual twisted product of the universal cocycle module with the group. -/
@[ext] structure UniversalExtension where
  kernel : UniversalModule G R
  quotient : G

namespace UniversalExtension
variable {G R}

instance : One (UniversalExtension G R) := ⟨⟨0, 1⟩⟩
instance : Mul (UniversalExtension G R) := ⟨fun x y =>
  ⟨x.kernel + universalActionLinear G R x.quotient y.kernel +
    universalPair G R x.quotient y.quotient, x.quotient * y.quotient⟩⟩
instance : Inv (UniversalExtension G R) := ⟨fun x =>
  ⟨-universalActionLinear G R x.quotient⁻¹
    (x.kernel + universalPair G R x.quotient x.quotient⁻¹), x.quotient⁻¹⟩⟩

@[simp] lemma one_kernel : (1 : UniversalExtension G R).kernel = 0 := rfl
@[simp] lemma one_quotient : (1 : UniversalExtension G R).quotient = 1 := rfl
@[simp] lemma mul_kernel (x y : UniversalExtension G R) :
    (x * y).kernel = x.kernel + universalActionLinear G R x.quotient y.kernel +
      universalPair G R x.quotient y.quotient := rfl
@[simp] lemma mul_quotient (x y : UniversalExtension G R) :
    (x * y).quotient = x.quotient * y.quotient := rfl

instance : Group (UniversalExtension G R) where
  mul_assoc x y z := by
    apply UniversalExtension.ext
    · simp only [mul_kernel, mul_quotient, map_add, universalActionLinear_mul,
        LinearMap.comp_apply]
      calc
        _ = x.kernel + universalActionLinear G R x.quotient y.kernel +
            universalActionLinear G R x.quotient
              (universalActionLinear G R y.quotient z.kernel) +
            (universalPair G R x.quotient y.quotient +
              universalPair G R (x.quotient * y.quotient) z.quotient) := by abel
        _ = _ := by
          rw [← universalPair_cocycle]
          abel
    · exact mul_assoc _ _ _
  one_mul x := by
    apply UniversalExtension.ext
    · simp only [mul_kernel, one_kernel, one_quotient, universalActionLinear_one,
        LinearMap.id_apply, universalPair_one_left, zero_add, add_zero]
    · exact one_mul _
  mul_one x := by
    apply UniversalExtension.ext
    · simp only [mul_kernel, one_kernel, one_quotient, map_zero,
        universalPair_one_right, add_zero]
    · exact mul_one _
  inv_mul_cancel x := by
    apply UniversalExtension.ext
    · change -universalActionLinear G R x.quotient⁻¹
          (x.kernel + universalPair G R x.quotient x.quotient⁻¹) +
        universalActionLinear G R x.quotient⁻¹ x.kernel +
          universalPair G R x.quotient⁻¹ x.quotient = 0
      have hc := universalPair_cocycle G R x.quotient⁻¹ x.quotient x.quotient⁻¹
      simp only [inv_mul_cancel, mul_inv_cancel, universalPair_one_right,
        universalPair_one_left, add_zero] at hc
      rw [map_add, hc]
      abel
    · exact inv_mul_cancel _

/-- The actual projection from the twisted group extension. -/
def projection : UniversalExtension G R →* G where
  toFun := quotient
  map_one' := rfl
  map_mul' _ _ := rfl

lemma projection_surjective : Function.Surjective (projection (G := G) (R := R)) :=
  fun g => ⟨⟨0, g⟩, rfl⟩

def pairEquiv : UniversalExtension G R ≃ UniversalModule G R × G where
  toFun x := (x.kernel, x.quotient)
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Fintype G] [Fintype R] : Fintype (UniversalExtension G R) :=
  Fintype.ofEquiv (UniversalModule G R × G) pairEquiv.symm

end UniversalExtension
end Paper18.Category.FiniteCohomologyKilling
