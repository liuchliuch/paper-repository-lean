import Paper20.YoungPathTableau

namespace Paper20.YoungShapes
open Finset
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- Consecutive entries of a genuine standard Young filling have distinct
contents. The proof inserts an actual intermediate cell if two equal
contents lie on the same diagonal, contradicting consecutive labels. -/
theorem adjacent_content_ne {n : ℕ} {μ : Shape n} (t : Path n μ)
    (i j : Fin n) (hij : j.val=i.val+1) : pathContent t i≠pathContent t j := by
  intro he
  let a := position t i
  let b := position t j
  have hc : (a.2:ℤ)-(a.1:ℤ)=(b.2:ℤ)-(b.1:ℤ) := he
  have hlt : i < j := by change i.val < j.val; omega
  have hreverse : ¬b≤a := position_not_reverse t i j hlt
  have hr : a.1 < b.1 := by
    by_contra hn
    apply hreverse
    exact ⟨by omega,by omega⟩
  have hcol : a.2 < b.2 := by omega
  have hm : (a.1,a.2+1) ∈ μ.val :=
    μ.val.isLowerSet (show (a.1,a.2+1)≤b from ⟨by omega,by omega⟩) (position_mem t j)
  let c : {c : ℕ × ℕ // c ∈ μ.val.cells} := ⟨(a.1,a.2+1),hm⟩
  let k := (positionEquiv t).symm c
  have hk : position t k=(a.1,a.2+1) := position_filling t c
  have hik : i < k := by
    apply index_lt_of_position_le t i k
    · rw [hk]
      change a≤(a.1,a.2+1)
      exact ⟨le_rfl,by omega⟩
    · intro hi
      have hp := congrArg (position t) hi
      rw [hk] at hp
      have hv := congrArg Prod.snd hp
      change a.2=a.2+1 at hv
      omega
  have hkj : k < j := by
    apply index_lt_of_position_le t k j
    · rw [hk]
      change (a.1,a.2+1)≤b
      exact ⟨by omega,by omega⟩
    · intro hj
      have hp := congrArg (position t) hj
      rw [hk] at hp
      have hv := congrArg Prod.fst hp
      change a.1=b.1 at hv
      omega
  have hi' : i.val < k.val := hik
  have hj' : k.val < j.val := hkj
  omega

end
end Paper20.YoungShapes
