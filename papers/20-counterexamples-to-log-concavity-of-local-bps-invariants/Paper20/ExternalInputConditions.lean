import Paper20.MathasInput

namespace Paper20.ExternalInput
open Paper20.ExternalNormalization Finset
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

/-- The precise genericity condition used in the external type-A
semisimplicity theorem holds at every permitted parameter. -/
theorem q_power_ne_one (v : K) (hp : Function.Injective (fun d : ℤ => v^d))
    (n : ℕ) (hn : 0 < n) : (v^2)^n≠1 := by
  intro he
  have hh : v^((2:ℤ)*(n:ℤ))=v^(0:ℤ) := by
    simpa only [zpow_mul,zpow_natCast,zpow_zero,zpow_ofNat,pow_zero] using he
  have hx := hp hh
  omega

theorem q_geometric_sum_ne_zero (v : K)
    (hp : Function.Injective (fun d : ℤ => v^d)) (n : ℕ) (hn : 0 < n) :
    (∑ j ∈ range n, (v^2)^j)≠0 := by
  intro he
  have hm := geom_sum_mul (v^2) n
  rw [he,zero_mul] at hm
  exact q_power_ne_one v hp n hn (sub_eq_zero.mp hm.symm)

/-- The type-A Mathas semisimplicity product is nonzero, for the actual
formal parameters, before invoking the registered character input. -/
theorem mathas_semisimplicity_product (r : ℕ) (v : K)
    (hp : Function.Injective (fun d : ℤ => v^d)) :
    (∏ i ∈ range r, (∑ j ∈ range (i+1), (v^2)^j))≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact q_geometric_sum_ne_zero v hp (i+1) (by omega)

lemma hook_quotient_product_ne_zero (v : K)
    (hp : Function.Injective (fun d : ℤ => v^d)) (hs : List ℕ)
    (hpos : ∀ a ∈ hs, 0 < a) :
    (hs.map (fun h => (1-(v^2)^h)/(1-v^2))).prod≠0 := by
  induction hs with
  | nil => simp
  | cons a hs ih =>
    simp only [List.map_cons,List.prod_cons]
    apply mul_ne_zero
    · apply div_ne_zero
      · exact sub_ne_zero.mpr (Ne.symm (q_power_ne_one v hp a (hpos a (by simp))))
      · have hn := q_power_ne_one v hp 1 (by decide)
        apply sub_ne_zero.mpr
        exact Ne.symm (by simpa only [pow_one] using hn)
    · exact ih (by intro h hh; exact hpos h (by simp [hh]))

theorem schurElement_ne_zero {r : ℕ} (p : Part r) (v : K) (hv : v≠0)
    (hp : Function.Injective (fun d : ℤ => v^d)) :
    schurElement (v^2) p.parts≠0 := by
  apply mul_ne_zero (zpow_ne_zero _ (pow_ne_zero 2 hv))
  apply hook_quotient_product_ne_zero v hp
  exact hooksOf_positive_of_mem_partitionsOf p.mem_partitionsOf

end
end Paper20.ExternalInput
