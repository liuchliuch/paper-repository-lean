import Paper12.StateVectors

noncomputable section
namespace Paper12
open Classical
variable {J : Type*} [Fintype J]

def hammingWeight (b : Basis J) : ℕ := ∑ x : J, (b x : ℕ)

theorem hammingWeight_oneHot (q : J) : hammingWeight (oneHot q) = 1 := by
  unfold hammingWeight
  rw [Finset.sum_eq_single q]
  · simp [oneHot]
  · intro x _ hx; simp [oneHot, hx]
  · intro hq; exact (hq (Finset.mem_univ _)).elim

theorem hammingWeight_eq_one (b : Basis J) :
    hammingWeight b = 1 ↔ ∃ q : J, b = oneHot q := by
  constructor
  · intro hw
    have hex : ∃ q : J, 0 < (b q : ℕ) := by
      by_contra hn
      push_neg at hn
      have hz : ∀ q : J, (b q : ℕ) = 0 := fun q => Nat.eq_zero_of_le_zero (hn q)
      simp [hammingWeight, hz] at hw
    obtain ⟨q, hq⟩ := hex
    have hbq : b q = 1 := Fin.ext (by have hlt := (b q).isLt; omega)
    refine ⟨q, ?_⟩
    have hs := Finset.sum_erase_add (s := (Finset.univ : Finset J))
      (f := fun x => (b x : ℕ)) (Finset.mem_univ q)
    have hz : ∑ x ∈ (Finset.univ : Finset J).erase q, (b x : ℕ) = 0 := by
      change _ = hammingWeight b at hs
      rw [hw] at hs
      dsimp only at hs
      have hv : (b q : ℕ) = 1 := by have hlt := (b q).isLt; omega
      omega
    funext x
    by_cases hx : x = q
    · subst x; simp [oneHot, hbq]
    · have hle := Finset.single_le_sum (s := (Finset.univ : Finset J).erase q)
        (f := fun x => (b x : ℕ)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_erase.mpr ⟨hx, Finset.mem_univ x⟩)
      rw [hz] at hle
      have hbx : b x = 0 := Fin.ext (Nat.eq_zero_of_le_zero hle)
      simp [oneHot, hx, hbx]
  · rintro ⟨q, rfl⟩
    exact hammingWeight_oneHot q

theorem weightedOneHot_off (d : J → ℝ) (b : Basis J) (hw : hammingWeight b ≠ 1) :
    weightedOneHot d b = 0 := by
  apply Finset.sum_eq_zero
  intro q _
  exact if_neg (fun h => hw (by rw [h, hammingWeight_oneHot]))
end Paper12
