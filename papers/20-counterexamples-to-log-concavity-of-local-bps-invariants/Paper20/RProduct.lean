import Paper20.SeriesIntegration

namespace Paper20.LogSeries
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

def affineBase : PowerSeries ℚ := 1+PowerSeries.C (1/4:ℚ)*PowerSeries.X

@[simp] theorem affineBase_constant : PowerSeries.constantCoeff affineBase = 1 := by
  simp [affineBase]

theorem affineBase_inverse : affineBase⁻¹ =
    PowerSeries.mk (fun i => (-1/4:ℚ)^i) := by
  apply (PowerSeries.inv_eq_iff_mul_eq_one (by simp)).2
  apply PowerSeries.ext
  intro i
  have he : PowerSeries.mk (fun i => (-1/4:ℚ)^i)*affineBase =
      PowerSeries.mk (fun i => (-1/4:ℚ)^i)+
        PowerSeries.C (1/4:ℚ)*(PowerSeries.X*PowerSeries.mk (fun i => (-1/4:ℚ)^i)) := by
    unfold affineBase
    ring
  rw [he]
  cases i with
  | zero => simp
  | succ i =>
    rw [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul]
    simp only [PowerSeries.coeff_mk, PowerSeries.coeff_one,
      if_neg (by omega : i+1 ≠ 0), pow_succ]
    ring

@[simp] theorem affineBase_inverse_coeff (i : ℕ) :
    PowerSeries.coeff i affineBase⁻¹ = (-1/4:ℚ)^i := by
  rw [affineBase_inverse, PowerSeries.coeff_mk]

def normalizedFactor (D : List ℚ) : PowerSeries ℚ :=
  PowerSeries.C (D.getD 0 0)*(polynomialSeries D)⁻¹

theorem normalizedFactor_derivative (D : List ℚ) :
    PowerSeries.derivative ℚ (normalizedFactor D) = negativeLog D*normalizedFactor D := by
  unfold normalizedFactor negativeLog
  rw [Derivation.leibniz, PowerSeries.derivative_C, PowerSeries.derivative_inv']
  simp only [smul_eq_mul, mul_zero, add_zero]
  ring

theorem normalizedFactor_constant (D : List ℚ) (hD : D.getD 0 0 ≠ 0) :
    PowerSeries.constantCoeff (normalizedFactor D) = 1 := by
  simp only [normalizedFactor, map_mul, PowerSeries.constantCoeff_C,
    PowerSeries.constantCoeff_inv, constant_polynomialSeries]
  exact mul_inv_cancel₀ hD

theorem derivative_power_log (F G : PowerSeries ℚ)
    (h : PowerSeries.derivative ℚ F = G*F) (m : ℕ) :
    PowerSeries.derivative ℚ (F^m) = PowerSeries.C (m:ℚ)*G*F^m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Derivation.leibniz, ih, h]
    push_cast
    simp only [map_add, map_one, smul_eq_mul]
    ring

theorem affineBase_inverse_derivative :
    PowerSeries.derivative ℚ affineBase⁻¹ =
      (-PowerSeries.C (1/4:ℚ)*affineBase⁻¹)*affineBase⁻¹ := by
  rw [PowerSeries.derivative_inv']
  have hd : PowerSeries.derivative ℚ affineBase = PowerSeries.C (1/4:ℚ) := by
    simp [affineBase, Derivation.leibniz]
  rw [hd]
  ring

theorem derivative_product (Ds : List (List ℚ)) :
    PowerSeries.derivative ℚ ((Ds.map normalizedFactor).prod) =
      (Ds.map negativeLog).sum*(Ds.map normalizedFactor).prod := by
  induction Ds with
  | nil => simp
  | cons D Ds ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    rw [Derivation.leibniz, normalizedFactor_derivative, ih]
    simp only [smul_eq_mul]
    ring

/-- The actual formal power series product specified in equation (18). -/
def Rproduct (hooks : List ℕ) (eEven : ℕ) : PowerSeries ℚ :=
  affineBase⁻¹^(eEven/2)*((hooks.map Dpoly).map normalizedFactor).prod

def logProduct (hooks : List ℕ) (eEven : ℕ) : PowerSeries ℚ :=
  -PowerSeries.C ((eEven/2:ℕ):ℚ)*PowerSeries.C (1/4:ℚ)*affineBase⁻¹+
    ((hooks.map Dpoly).map negativeLog).sum

/-- Product differentiation establishes the logarithmic-derivative equation
for (18); its recurrence is not assumed. -/
theorem Rproduct_derivative (hooks : List ℕ) (eEven : ℕ) :
    PowerSeries.derivative ℚ (Rproduct hooks eEven) =
      logProduct hooks eEven*Rproduct hooks eEven := by
  unfold Rproduct logProduct
  rw [Derivation.leibniz, derivative_product,
    derivative_power_log _ _ affineBase_inverse_derivative]
  simp only [smul_eq_mul]
  ring

theorem Rproduct_constant (hooks : List ℕ) (eEven : ℕ)
    (hh : ∀ a ∈ hooks, 1 ≤ a) : PowerSeries.coeff 0 (Rproduct hooks eEven) = 1 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  unfold Rproduct
  rw [map_mul, map_pow, PowerSeries.constantCoeff_inv, affineBase_constant, inv_one, one_pow,
    one_mul]
  have hprod : ∀ Ds : List (List ℚ), (∀ D ∈ Ds, D.getD 0 0 ≠ 0) →
      PowerSeries.constantCoeff ((Ds.map normalizedFactor).prod) = 1 := by
    intro Ds hDs
    induction Ds with
    | nil => simp
    | cons D Ds ih =>
      simp only [List.map_cons, List.prod_cons, map_mul]
      rw [normalizedFactor_constant D (hDs D (by simp)),
        ih (fun d hd => hDs d (by simp [hd])), one_mul]
  apply hprod
  intro D hD
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hD
  exact ne_of_gt (Dconst_pos a (hh a ha))

end
end Paper20.LogSeries
