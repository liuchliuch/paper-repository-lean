import Paper20.RSeriesFieldEvaluation
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.Localization.FractionRing

namespace Paper20.QuantumSeriesCoordinates
open Polynomial
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

abbrev SeriesField := FractionRing (PowerSeries ℚ)

local instance : CharZero (PowerSeries ℚ) :=
  charZero_of_injective_ringHom (f:=PowerSeries.C)
    PowerSeries.C_injective

instance : CharZero SeriesField :=
  charZero_of_injective_ringHom (f:=algebraMap (PowerSeries ℚ) SeriesField)
    (IsFractionRing.injective (PowerSeries ℚ) SeriesField)

def embedding : PowerSeries ℚ →ₐ[ℚ] SeriesField :=
  IsScalarTower.toAlgHom ℚ (PowerSeries ℚ) SeriesField

theorem embedding_injective : Function.Injective embedding :=
  IsFractionRing.injective (PowerSeries ℚ) SeriesField

def V : PowerSeries ℚ := 1+PowerSeries.X
def W : PowerSeries ℚ := (V-V⁻¹)^2

@[simp] theorem V_constant : PowerSeries.constantCoeff V=1 := by simp [V]
@[simp] theorem V_inverse_constant : PowerSeries.constantCoeff V⁻¹=1 := by simp
@[simp] theorem W_constant : PowerSeries.constantCoeff W=0 := by simp [W]

theorem V_inverse_coeff_one : PowerSeries.coeff 1 V⁻¹ = -1 := by
  have he := congrArg (PowerSeries.coeff 1)
    (PowerSeries.mul_inv_cancel V (by simp))
  rw [PowerSeries.coeff_one_mul] at he
  norm_num [V] at he ⊢
  linarith

theorem difference_ne_zero : V-V⁻¹ ≠ 0 := by
  intro h
  have he := congrArg (PowerSeries.coeff 1) h
  simp only [map_sub,V_inverse_coeff_one,map_zero] at he
  norm_num [V] at he

theorem W_ne_zero : W ≠ 0 := pow_ne_zero 2 difference_ne_zero

def W_hasSubst : PowerSeries.HasSubst W :=
  PowerSeries.HasSubst.of_constantCoeff_zero' W_constant

/-- Substitution by a nonzero zero-constant series is faithful. Factor a
nonzero input into X^order times a genuine unit, then map both factors. -/
theorem subst_injective (a : PowerSeries ℚ) (ha : PowerSeries.HasSubst a) (hne : a ≠ 0) :
    Function.Injective (PowerSeries.substAlgHom (R:=ℚ) ha) := by
  let φ := PowerSeries.substAlgHom (R:=ℚ) ha
  have hn : ∀ f : PowerSeries ℚ, f ≠ 0 → φ f ≠ 0 := by
    intro f hf
    have hu : IsUnit (PowerSeries.divXPowOrder f) := by
      apply PowerSeries.isUnit_iff_constantCoeff.mpr
      apply isUnit_iff_ne_zero.mpr
      exact fun h => hf (PowerSeries.constantCoeff_divXPowOrder_eq_zero_iff.mp h)
    have hφ : IsUnit (φ (PowerSeries.divXPowOrder f)) := hu.map φ.toMonoidHom
    rw [← PowerSeries.X_pow_order_mul_divXPowOrder (f:=f),map_mul,map_pow]
    have hx : φ PowerSeries.X=a := PowerSeries.substAlgHom_X ha
    rw [hx]
    exact mul_ne_zero (pow_ne_zero _ hne) hφ.ne_zero
  intro f g h
  by_contra hnefg
  have hz : φ (f-g)=0 := by rw [map_sub,h,sub_self]
  exact hn (f-g) (sub_ne_zero.mpr hnefg) hz

/-- The concrete formal coordinate change w=(v-v^-1)^2, with v=1+t,
followed by the injective embedding into the Laurent fraction field. -/
def coordinateMap : PowerSeries ℚ →ₐ[ℚ] SeriesField :=
  embedding.comp (PowerSeries.substAlgHom (R:=ℚ) W_hasSubst)

theorem coordinateMap_injective : Function.Injective coordinateMap :=
  embedding_injective.comp (subst_injective W W_hasSubst W_ne_zero)

def v : SeriesField := embedding V

lemma v_inverse : embedding V⁻¹=v⁻¹ := seriesHom_inv embedding V (by simp)

theorem v_ne_zero : v ≠ 0 := by
  apply (map_ne_zero_iff embedding embedding_injective).2
  intro h
  have he := congrArg PowerSeries.constantCoeff h
  simpa using he

theorem quantum_difference_ne_zero : v-v⁻¹ ≠ 0 := by
  change embedding V-v⁻¹ ≠ 0
  rw [← v_inverse,← map_sub]
  exact (map_ne_zero_iff embedding embedding_injective).2 difference_ne_zero

theorem quantum_sum_ne_zero : v+v⁻¹ ≠ 0 := by
  change embedding V+v⁻¹ ≠ 0
  rw [← v_inverse,← map_add]
  apply (map_ne_zero_iff embedding embedding_injective).2
  intro h
  have he := congrArg PowerSeries.constantCoeff h
  norm_num at he

theorem coordinateMap_X : coordinateMap PowerSeries.X=(v-v⁻¹)^2 := by
  rw [coordinateMap,AlgHom.comp_apply,PowerSeries.substAlgHom_X,W,map_pow,map_sub,v_inverse]
  rfl

/-- Equation (21) for the actual r=36 normalized formal series under a
proved injective, explicit change of formal coordinates. -/
theorem normalized_series_quantum_trace (k : ℕ) :
    coordinateMap (normalizedPartitionSeries 36 k)=quantumPartitionTrace 36 k v :=
  normalizedPartitionSeries36_quantumTrace coordinateMap k v v_ne_zero
    quantum_difference_ne_zero quantum_sum_ne_zero coordinateMap_X

end
end Paper20.QuantumSeriesCoordinates
