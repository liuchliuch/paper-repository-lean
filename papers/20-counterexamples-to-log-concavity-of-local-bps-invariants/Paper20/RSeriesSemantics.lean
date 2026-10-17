import Paper20.RProduct

namespace Paper20.LogSeries
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

lemma parity_term (m i : ℕ) : -(m:ℚ)*(1/4:ℚ)*(-1/4:ℚ)^i =
    (m:ℚ)*(if (i+1)%2=0 then 1 else -1)/(4^(i+1):ℕ) := by
  have hs : (if (i+1)%2=0 then 1 else -1:ℚ) = (-1:ℚ)^(i+1) := by
    rw [neg_one_pow_eq_ite]
    simp only [Nat.even_iff]
  rw [hs]
  push_cast
  rw [div_pow, pow_succ, pow_succ]
  field_simp <;> ring

lemma foldl_sum_rat {α : Type*} (f : α → ℚ) (as : List α) (z : ℚ) :
    as.foldl (fun acc a => acc+f a) z = z+(as.map f).sum := by
  induction as generalizing z with
  | nil => simp
  | cons a as ih => simp only [List.foldl_cons, ih, List.map_cons, List.sum_cons]; ring

theorem logProduct_coeff (hooks : List ℕ) (eEven i : ℕ) :
    PowerSeries.coeff i (logProduct hooks eEven) =
      (hooks.map (fun a => PowerSeries.coeff i (negativeLog (Dpoly a)))).sum+
        (((eEven/2:ℕ):ℚ)*(if (i+1)%2=0 then 1 else -1)/(4^(i+1):ℕ)) := by
  unfold logProduct
  rw [map_add]
  have he : -PowerSeries.C ((eEven/2:ℕ):ℚ)*PowerSeries.C (1/4:ℚ)*affineBase⁻¹ =
      -(PowerSeries.C ((eEven/2:ℕ):ℚ)*(PowerSeries.C (1/4:ℚ)*affineBase⁻¹)) := by ring
  rw [he, map_neg, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
    affineBase_inverse_coeff]
  rw [map_list_sum]
  simp only [List.map_map, Function.comp_def]
  have hs := parity_term (eEven/2) i
  linear_combination (norm := ring_nf) hs

/-- Equation (28)'s exact finite gamma list is the logarithmic derivative
of the genuine product (18), through all requested coefficients. -/
theorem gammaSeries_correct (hooks : List ℕ) (eEven H i : ℕ)
    (hh : ∀ a ∈ hooks, 1 ≤ a) (hi : i < H) :
    (gammaSeries hooks eEven H).getD (i+1) 0 =
      PowerSeries.coeff i (logProduct hooks eEven) := by
  unfold gammaSeries
  rw [List.getD_eq_getD_getElem?, List.getElem?_map,
    List.getElem?_range (by omega), Option.map_some, Option.getD_some]
  simp only [if_neg (by omega : i+1 ≠ 0), Nat.add_sub_cancel]
  rw [foldl_sum_rat, zero_add, logProduct_coeff]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  apply negDLog_correct _ _ H i hi
  exact ne_of_gt (Dconst_pos a (hh a ha))

/-- Every retained coefficient of the actual `Rseries` implementation is
the coefficient of the exact power-series product in equation (18). -/
theorem Rseries_correct (hooks : List ℕ) (eEven H j : ℕ)
    (hh : ∀ a ∈ hooks, 1 ≤ a) (hj : j ≤ H) :
    (Rseries hooks eEven H).getD j 0 = PowerSeries.coeff j (Rproduct hooks eEven) := by
  apply rFromGamma_correct (gammaSeries hooks eEven H) (Rproduct hooks eEven)
    (logProduct hooks eEven) (Rproduct_constant hooks eEven hh)
    (Rproduct_derivative hooks eEven) H _ j hj
  intro i hi
  exact gammaSeries_correct hooks eEven H i hh hi

end
end Paper20.LogSeries
