import PUT.FiniteRegisters
import PUT.CollisionCircuit

/-!
# Qubit encoding of the actual full collision circuit

The reversible collision oracle retains both the input label and a scratch
register. Its actual garbage dimension is `(D+R)*D`, rather than `D+R`.
This module encodes that complete circuit, including its scratch and arbitrary
input action, in `2 + 3 ceil(log₂(D+R))` qubits. It does not remove a scratch
register merely because that register is clean on the designated input.
-/
noncomputable section
namespace PUT.CollisionRegisters
open PUT.QueryModel PUT.CollisionCircuit PUT.CollisionReduction
open scoped InnerProductSpace

/-- Oracle qubits for the full reversible collision construction. -/
def qubits (d : ℕ) : ℕ := 2 + 3 * Nat.clog 2 d

/-- The actual label/input/scratch basis has dimension `1 + d²D`. -/
theorem physical_dimension (D R : ℕ) :
    Fintype.card (HQ (D+R) ((D+R)*D)) = 1 + (D+R)^2*D := by
  simp [HQ, pow_two, mul_assoc]

/-- The retained scratch still leaves a cubic physical dimension. -/
theorem physical_dimension_le_cubic (D R : ℕ) :
    Fintype.card (HQ (D+R) ((D+R)*D)) ≤ 1 + (D+R)^3 := by
  rw [physical_dimension]
  have hD : D ≤ D+R := by omega
  have hmul := Nat.mul_le_mul_left ((D+R)^2) hD
  have hpow : (D+R)^2*(D+R) = (D+R)^3 := by ring
  rw [hpow] at hmul
  exact Nat.add_le_add_left hmul 1

/-- Enough actual computational basis vectors for the full oracle. -/
theorem physical_capacity {D R : ℕ} (hd : 2 ≤ D+R) :
    Fintype.card (HQ (D+R) ((D+R)*D)) ≤ 2 ^ qubits (D+R) := by
  have hd1 : 1 ≤ D+R := by omega
  have hc : 1 ≤ (D+R)^3 := one_le_pow₀ hd1
  have hp := Nat.le_pow_clog (by norm_num : 1 < 2) (D+R)
  have hp3 := Nat.pow_le_pow_left hp 3
  unfold qubits
  calc
    _ ≤ 1 + (D+R)^3 := physical_dimension_le_cubic D R
    _ ≤ 4 * (D+R)^3 := by omega
    _ ≤ 4 * (2 ^ Nat.clog 2 (D+R))^3 := Nat.mul_le_mul_left 4 hp3
    _ = 2 ^ (2 + 3 * Nat.clog 2 (D+R)) := by
      simp only [← pow_mul, pow_add]
      ring

/-- An actual isometric embedding of the complete query register into qubits. -/
def embedding {D R : ℕ} (hd : 2 ≤ D+R) :
    PurificationSpace (D+R) ((D+R)*D) →ₗᵢ[ℂ]
      EuclideanSpace ℂ (Fin (2 ^ qubits (D+R))) :=
  FiniteRegisters.finiteQubitEmbedding (HQ (D+R) ((D+R)*D)) (qubits (D+R))
    (physical_capacity hd)

/-- Explicit logarithmic qubit bound, for the actual larger garbage space. -/
theorem qubits_log_bound {d : ℕ} (hd : 2 ≤ d) :
    (qubits d : ℝ) ≤ 5 + 3 * Real.logb 2 d := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hlog : 0 ≤ Real.logb 2 d := Real.logb_nonneg (by norm_num) hdR
  have hceil := (Nat.ceil_lt_add_one hlog).le
  have he : ⌈Real.logb 2 (d : ℝ)⌉₊ = Nat.clog 2 d := Real.natCeil_logb_natCast 2 d
  rw [he] at hceil
  unfold qubits
  push_cast
  linarith

variable {D R : ℕ} [NeZero D]

/-- The full unknown collision oracle, extended by the same known `-I` on
all unused qubit coordinates. This is a genuine surjective unitary. -/
def encodedUnitary (hd : 2 ≤ D+R) (f : Fin D → Fin D) :
    EuclideanSpace ℂ (Fin (2 ^ qubits (D+R))) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Fin (2 ^ qubits (D+R))) :=
  FiniteRegisters.extendUnitary (embedding hd) (physicalUnitary (R := R) f)

/-- The complete original action is preserved on every embedded input. -/
theorem encodedUnitary_on_image (hd : 2 ≤ D+R) (f : Fin D → Fin D)
    (v : PurificationSpace (D+R) ((D+R)*D)) :
    encodedUnitary hd f (embedding hd v) = embedding hd (physicalUnitary f v) :=
  FiniteRegisters.extendUnitary_on_image (embedding hd) (physicalUnitary f) v

/-- The actual prepared state includes a clean scratch component, and is
encoded exactly; no other input action has been discarded. -/
theorem encodedUnitary_prepares (hd : 2 ≤ D+R) (f : Fin D → Fin D) :
    encodedUnitary hd f (embedding hd (zeroState (D+R) ((D+R)*D))) =
      embedding hd (∑ x : Fin (D+R), EuclideanSpace.single
        (Sum.inr (extend f x, finProdFinEquiv (x, (0 : Fin D))))
          ((Real.sqrt (D+R : ℕ) : ℂ)⁻¹)) := by
  rw [encodedUnitary_on_image, physicalUnitary_prepares]

/-- The added coordinates have a fixed full operator action independent of `f`. -/
theorem encodedUnitary_on_complement (hd : 2 ≤ D+R) (f : Fin D → Fin D)
    (y : EuclideanSpace ℂ (Fin (2 ^ qubits (D+R))))
    (hy : ∀ v : PurificationSpace (D+R) ((D+R)*D), inner ℂ (embedding hd v) y = 0) :
    encodedUnitary hd f y = -y :=
  FiniteRegisters.extendUnitary_on_complement (embedding hd) (physicalUnitary f) y hy

/-- A concrete logarithmic-size realization for every actual collision oracle. -/
theorem finite_collision_realization (hd : 2 ≤ D+R) :
    ∃ (q : ℕ) (J : PurificationSpace (D+R) ((D+R)*D) →ₗᵢ[ℂ]
        EuclideanSpace ℂ (Fin (2 ^ q))),
      (q : ℝ) ≤ 5 + 3 * Real.logb 2 (D+R : ℕ) ∧
      ∀ (f : Fin D → Fin D) (v : PurificationSpace (D+R) ((D+R)*D)),
        FiniteRegisters.extendUnitary J (physicalUnitary f) (J v) = J (physicalUnitary f v) := by
  exact ⟨qubits (D+R), embedding hd, qubits_log_bound hd,
    fun f v => FiniteRegisters.extendUnitary_on_image (embedding hd) (physicalUnitary f) v⟩

end PUT.CollisionRegisters
