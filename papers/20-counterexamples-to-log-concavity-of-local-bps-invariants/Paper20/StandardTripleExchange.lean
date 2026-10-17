import Paper20.StandardExchangeDisjoint
import Paper20.HeckeRelations

namespace Paper20.YoungShapes
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

lemma exchangeable_after_first {n : ℕ} {μ : Shape n} (t : StandardFilling μ)
    (i j k : Fin n) (hij : j.val=i.val+1) (hi : Exchangeable t i j)
    (hik : i≠k) (hjk : j≠k) :
    Exchangeable (exchange t i j hij hi) j k ↔ Exchangeable t i k := by
  simp only [Exchangeable,exchange_apply,Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne hik.symm hjk.symm]

lemma exchangeable_after_second {n : ℕ} {μ : Shape n} (t : StandardFilling μ)
    (i j k : Fin n) (hjk : k.val=j.val+1) (hj : Exchangeable t j k)
    (hij : i≠j) (hik : i≠k) :
    Exchangeable (exchange t j k hjk hj) i j ↔ Exchangeable t i k := by
  simp only [Exchangeable,exchange_apply,Equiv.swap_apply_left,
    Equiv.swap_apply_of_ne_of_ne hij hik]

lemma exchangeable_after_first_second {n : ℕ} {μ : Shape n} (t : StandardFilling μ)
    (i j k : Fin n) (hij : j.val=i.val+1) (hjk : k.val=j.val+1)
    (hi : Exchangeable t i j) (hu : Exchangeable (exchange t i j hij hi) j k)
    (hij' : i≠j) (hik : i≠k) (hjk' : j≠k) :
    Exchangeable (exchange (exchange t i j hij hi) j k hjk hu) i j ↔ Exchangeable t j k := by
  simp only [Exchangeable,exchange_apply,Equiv.swap_apply_left,Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne hij' hik,
    Equiv.swap_apply_of_ne_of_ne hik.symm hjk'.symm]

lemma exchangeable_after_second_first {n : ℕ} {μ : Shape n} (t : StandardFilling μ)
    (i j k : Fin n) (hij : j.val=i.val+1) (hjk : k.val=j.val+1)
    (hj : Exchangeable t j k) (hv : Exchangeable (exchange t j k hjk hj) i j)
    (hij' : i≠j) (hik : i≠k) (hjk' : j≠k) :
    Exchangeable (exchange (exchange t j k hjk hj) i j hij hv) j k ↔ Exchangeable t i j := by
  simp only [Exchangeable,exchange_apply,Equiv.swap_apply_left,Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne hij' hik,
    Equiv.swap_apply_of_ne_of_ne hik.symm hjk'.symm]

/-- Whenever the two genuine length-three exchange paths stay standard,
their resulting fillings agree, by the actual permutation braid relation. -/
theorem exchange_braid {n : ℕ} {μ : Shape n} (t : StandardFilling μ)
    (i j k : Fin n) (hij : j.val=i.val+1) (hjk : k.val=j.val+1)
    (hi : Exchangeable t i j) (hj : Exchangeable t j k)
    (hu : Exchangeable (exchange t i j hij hi) j k)
    (hv : Exchangeable (exchange t j k hjk hj) i j)
    (huv : Exchangeable (exchange (exchange t i j hij hi) j k hjk hu) i j)
    (hvu : Exchangeable (exchange (exchange t j k hjk hj) i j hij hv) j k) :
    exchange (exchange (exchange t i j hij hi) j k hjk hu) i j hij huv=
      exchange (exchange (exchange t j k hjk hj) i j hij hv) j k hjk hvu := by
  have hneij : i≠j := by intro h; have := congrArg Fin.val h; omega
  have hnejk : j≠k := by intro h; have := congrArg Fin.val h; omega
  have hneik : i≠k := by intro h; have := congrArg Fin.val h; omega
  apply Subtype.ext
  apply Equiv.ext
  intro a
  simp only [exchange_apply]
  have hm := Paper20.HeckeOperators.swap_braid i j k hneij hnejk hneik
  exact congrArg (fun σ : Equiv.Perm (Fin n) => t.val (σ a)) hm

end
end Paper20.YoungShapes
