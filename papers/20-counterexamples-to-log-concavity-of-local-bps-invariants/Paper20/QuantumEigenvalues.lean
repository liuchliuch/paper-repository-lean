import Paper20.YoungAdjacentContents
import Paper20.HilbertAtZero

namespace Paper20.Seminormal
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

lemma zpow_injective_of_nat {F : Type*} [Field F] (v : F) (hv : v≠0)
    (hp : ∀ n : ℕ, v^n=1 → n=0) : Function.Injective (fun d : ℤ => v^d) := by
  have hz : ∀ d : ℤ, v^d=1 → d=0 := by
    intro d hd
    cases d with
    | ofNat n =>
      have hn := hp n (by simpa only [Int.ofNat_eq_natCast,zpow_natCast] using hd)
      simp only [hn,Int.ofNat_eq_natCast,Int.natCast_zero]
    | negSucc n =>
      rw [zpow_negSucc] at hd
      have hn := hp (n+1) (inv_eq_one.mp hd)
      omega
  intro a b hab
  dsimp only at hab
  apply sub_eq_zero.mp
  apply hz
  rw [zpow_sub₀ hv,hab,div_self (zpow_ne_zero _ hv)]

open Paper20.QuantumSeriesCoordinates

/-- The actual formal parameter v=1+t has infinite multiplicative order,
as witnessed by the coefficient of t in every positive power. -/
theorem hilbert_unit_parameter_injective : Function.Injective (fun d : ℤ => v^d) := by
  apply zpow_injective_of_nat v v_ne_zero
  intro n hn
  have he : V^n=1 := embedding_injective (by simpa only [map_pow,map_one] using hn)
  have hc := congrArg (PowerSeries.coeff 1) he
  norm_num [PowerSeries.coeff_one_pow,V] at hc
  exact_mod_cast hc

/-- The actual Hilbert-origin parameter v=t has infinite multiplicative
order, as witnessed already by the constant coefficient of positive powers. -/
theorem hilbert_origin_parameter_injective :
    Function.Injective (fun d : ℤ => HilbertAtZero.v^d) := by
  apply zpow_injective_of_nat HilbertAtZero.v HilbertAtZero.v_ne_zero
  intro n hn
  by_contra hne
  have he : (PowerSeries.X:PowerSeries ℚ)^n=1 :=
    embedding_injective (by simpa only [map_pow,map_one] using hn)
  have hc := congrArg PowerSeries.constantCoeff he
  simp only [map_pow,PowerSeries.constantCoeff_X,zero_pow hne,map_one] at hc
  exact zero_ne_one hc

/-- The seminormal denominator for actual adjacent tableau labels is
nonzero whenever the chosen quantum parameter has the proved faithful
integer-power map. -/
theorem adjacent_denominator_ne_zero {F : Type*} [Field F] (v : F)
    (hv : Function.Injective (fun d : ℤ => v^d))
    {n : ℕ} {μ : YoungShapes.Shape n} (t : YoungShapes.Path n μ)
    (i j : Fin n) (hij : j.val=i.val+1) :
    v^(2*YoungShapes.pathContent t j)-v^(2*YoungShapes.pathContent t i)≠0 := by
  apply sub_ne_zero.mpr
  intro he
  have hc := hv he
  have hc' : YoungShapes.pathContent t i=YoungShapes.pathContent t j := by omega
  exact YoungShapes.adjacent_content_ne t i j hij hc'

end
end Paper20.Seminormal
