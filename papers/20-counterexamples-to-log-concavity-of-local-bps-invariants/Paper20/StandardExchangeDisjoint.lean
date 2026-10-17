import Paper20.StandardContents

namespace Paper20.YoungShapes
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

/-- Exchanging disjoint labels preserves the actual comparability test
for a second pair. -/
theorem exchangeable_other {n : ℕ} {μ : Shape n} (t : StandardFilling μ)
    (i j k l : Fin n) (hij : j.val=i.val+1) (h : Exchangeable t i j)
    (hik : i≠k) (hil : i≠l) (hjk : j≠k) (hjl : j≠l) :
    Exchangeable (exchange t i j hij h) k l ↔ Exchangeable t k l := by
  simp only [Exchangeable,exchange_apply,
    Equiv.swap_apply_of_ne_of_ne hik.symm hjk.symm,
    Equiv.swap_apply_of_ne_of_ne hil.symm hjl.symm]

/-- The actual valid exchanges commute when their label pairs are
disjoint, with every intermediate standard-filling proof retained. -/
theorem exchange_commute {n : ℕ} {μ : Shape n} (t : StandardFilling μ)
    (i j k l : Fin n) (hij : j.val=i.val+1) (hkl : l.val=k.val+1)
    (hik : i≠k) (hil : i≠l) (hjk : j≠k) (hjl : j≠l)
    (hi : Exchangeable t i j) (hk : Exchangeable t k l)
    (hk' : Exchangeable (exchange t i j hij hi) k l)
    (hi' : Exchangeable (exchange t k l hkl hk) i j) :
    exchange (exchange t i j hij hi) k l hkl hk'=
      exchange (exchange t k l hkl hk) i j hij hi' := by
  apply Subtype.ext
  apply Equiv.ext
  intro a
  simp only [exchange_apply]
  have hm : Equiv.swap i j*Equiv.swap k l=Equiv.swap k l*Equiv.swap i j := by
    rw [Equiv.mul_swap_eq_swap_mul,
      Equiv.swap_apply_of_ne_of_ne hik.symm hjk.symm,
      Equiv.swap_apply_of_ne_of_ne hil.symm hjl.symm]
  exact congrArg (fun σ : Equiv.Perm (Fin n) => t.val (σ a)) hm

/-- The actual adjacent-tableau move fixes the state when its exchange
is forbidden, and performs the proved standard exchange otherwise. -/
def exchangeMove {n : ℕ} {μ : Shape n} (i j : Fin n) (hij : j.val=i.val+1)
    (t : StandardFilling μ) : StandardFilling μ :=
  if h : Exchangeable t i j then exchange t i j hij h else t

/-- The concrete adjacent-tableau move is an involution. -/
theorem exchangeMove_involutive {n : ℕ} {μ : Shape n} (i j : Fin n)
    (hij : j.val=i.val+1) : Function.Involutive (exchangeMove (μ:=μ) i j hij) := by
  intro t
  by_cases h : Exchangeable t i j
  · have h' : Exchangeable (exchange t i j hij h) i j := exchange_incomparable t i j hij h
    simp only [exchangeMove,dif_pos h,dif_pos h',exchange_exchange]
  · simp only [exchangeMove,dif_neg h]

end
end Paper20.YoungShapes
