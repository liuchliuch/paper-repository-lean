import K44K35Free.Cap
import Mathlib.FieldTheory.Finite.GaloisField

/-! Existence of the finite fields used in the final construction. -/
namespace K44K35Free

/-- Every nonzero power of three is realized by an odd finite field, with an
actual nonsquare parameter as required by the point-set construction. -/
theorem exists_field_three_power (k : ℕ) (hk : k ≠ 0) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F),
      Fintype.card F = 3 ^ k ∧ Odd (Fintype.card F) ∧ ∃ α : F, IsNonsquare α := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let F := GaloisField 3 k
  letI : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = 3 ^ k := by
    exact (Nat.card_eq_fintype_card).symm.trans (GaloisField.card 3 k hk)
  have hchar : ringChar F = 3 := ringChar.eq F 3
  obtain ⟨α, hα⟩ := FiniteField.exists_nonsquare (F := F) (by omega : ringChar F ≠ 2)
  refine ⟨F, inferInstance, inferInstance, hc, ?_, α, ?_⟩
  · rw [hc]
    exact (by decide : Odd (3 : ℕ)).pow
  · intro a ha
    apply hα
    exact ⟨a, by simpa [pow_two] using ha.symm⟩

end K44K35Free
