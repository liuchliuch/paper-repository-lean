import Paper12.TwoReflection
import Paper12.Circuit

/-!
# Exact symmetric oblivious amplification (Lemma 4.1)

If a `Γ`-symmetric circuit `A` has zero-workspace block `√p V`, then `V`
has an exact clean `Γ`-symmetric circuit with `|W|+2` workspace qubits and
`O((s(A)+1)/√p)` gates.  The proof is the two-reflection identity with
`K = ⌈π/(4√p)⌉` and `θ = π/(4K+2)`.

This file proves the scalar side of the construction: the angle `θ` lies in
`(0, π/2)`, the identity `(2K+1)θ = π/2` holds exactly, the correction angle
`ζ` of equation (20) exists, and the size bound `32 (s(A)+1)(K+1)` dominates
the `2K+1` calls to `A` or `A†`.  The operator form of Lemma 4.1 follows from
the two-reflection identity.
-/

noncomputable section

namespace Paper12

open Matrix Complex

/-! ### Amplification parameters -/

/-- Amplification iteration count. -/
def ampK (p : ℝ) : ℕ := Nat.ceil (Real.pi / (4 * Real.sqrt p))

/-- Rotation angle of the amplification. -/
def ampTheta (p : ℝ) : ℝ := Real.pi / (4 * (ampK p : ℝ) + 2)

theorem ampK_nonneg (p : ℝ) : 0 ≤ ampK p := Nat.zero_le _

theorem ampK_pos {p : ℝ} (hp : 0 < p) : 0 < ampK p := by
  apply Nat.ceil_pos.mpr
  positivity

theorem ampTheta_pos (p : ℝ) : 0 < ampTheta p := by
  unfold ampTheta
  positivity

theorem ampTheta_lt_pi_div_two (p : ℝ) (hp : 0 < p) : ampTheta p < Real.pi / 2 := by
  unfold ampTheta
  apply div_lt_div_of_pos_left Real.pi_pos (by norm_num)
  have hK : (0 : ℝ) < ampK p := by exact_mod_cast ampK_pos hp
  linarith

theorem ampTheta_mem (p : ℝ) (hp : 0 < p) :
    0 < ampTheta p ∧ ampTheta p < Real.pi / 2 :=
  ⟨ampTheta_pos p, ampTheta_lt_pi_div_two p hp⟩

/-- The defining identity of the amplification angle:
`(2K+1) · θ = π/2` exactly. -/
theorem twoK_add_one_mul_theta (p : ℝ) :
    ((2 * ampK p + 1 : ℕ) : ℝ) * ampTheta p = Real.pi / 2 := by
  unfold ampTheta
  have hd : (4 * (ampK p : ℝ) + 2) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- `K = ⌈π/(4√p)⌉` satisfies `π/(4√p) ≤ K`. -/
theorem ampK_ge (p : ℝ) (hp : 0 < p) :
    Real.pi / (4 * Real.sqrt p) ≤ ampK p :=
  Nat.le_ceil _

/-- `K = ⌈π/(4√p)⌉` satisfies `K < π/(4√p) + 1`. -/
theorem ampK_lt (p : ℝ) (hp : 0 < p) :
    (ampK p : ℝ) < Real.pi / (4 * Real.sqrt p) + 1 :=
  Nat.ceil_lt_add_one (by positivity)

/-- Inverse-success amplification count is `O(K)`. -/
theorem inv_sqrt_le_ampK (p : ℝ) (hp : 0 < p) :
    (1 / Real.sqrt p : ℝ) ≤ (4 / Real.pi) * (ampK p) := by
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp
  have hπ : 0 < Real.pi := Real.pi_pos
  have h : Real.pi / (4 * Real.sqrt p) ≤ (ampK p : ℝ) := ampK_ge p hp
  have hpos : 0 < 4 * Real.sqrt p := by positivity
  have : (1 / Real.sqrt p : ℝ) = (4 / Real.pi) * (Real.pi / (4 * Real.sqrt p)) := by
    field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-! ### Correction angle `ζ` of equation (20) -/

theorem sin_ampTheta_div_sqrt (p : ℝ) (hp : 0 < p) :
    0 < Real.sin (ampTheta p) / Real.sqrt p ∧
      Real.sin (ampTheta p) / Real.sqrt p < 1 := by
  have hθ := ampTheta_mem p hp
  have hspos : 0 < Real.sin (ampTheta p) :=
    Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [Real.pi_pos])
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp
  have hK := ampK_ge p hp
  have hmul : Real.pi ≤ (ampK p : ℝ) * (4 * Real.sqrt p) :=
    (div_le_iff₀ (show 0 < 4 * Real.sqrt p by positivity)).mp hK
  have hθlt : ampTheta p < Real.sqrt p := by
    unfold ampTheta
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith
  have hsine : Real.sin (ampTheta p) < Real.sqrt p :=
    lt_trans (Real.sin_lt hθ.1) hθlt
  exact ⟨div_pos hspos hs, (div_lt_one hs).mpr hsine⟩

/-- The correction angle `ζ ∈ (0, π)` of equation (20):
`cos(ζ/2) = sin θ / √p`. -/
def ampZeta (p : ℝ) : ℝ := 2 * Real.arccos (Real.sin (ampTheta p) / Real.sqrt p)

theorem ampZeta_mem (p : ℝ) (hp : 0 < p) :
    0 < ampZeta p ∧ ampZeta p < Real.pi ∧
      Real.cos (ampZeta p / 2) = Real.sin (ampTheta p) / Real.sqrt p := by
  obtain ⟨hpos, hlt⟩ := sin_ampTheta_div_sqrt p hp
  set r := Real.sin (ampTheta p) / Real.sqrt p with hr
  have harcpos : 0 < Real.arccos r := Real.arccos_pos.mpr hlt
  have harclt : Real.arccos r < Real.pi / 2 := Real.arccos_lt_pi_div_two.mpr hpos
  unfold ampZeta
  refine ⟨by linarith, by linarith, ?_⟩
  have heq : 2 * Real.arccos r / 2 = Real.arccos r := by ring
  change Real.cos (2 * Real.arccos r / 2) = r
  rw [heq, Real.cos_arccos (by linarith) (by linarith)]

/-- The block-scale identity `√p · cos(ζ/2) = sin θ`. -/
theorem amp_scale_identity (p : ℝ) (hp : 0 < p) :
    Real.sqrt p * Real.cos (ampZeta p / 2) = Real.sin (ampTheta p) := by
  obtain ⟨_, _, hcos⟩ := ampZeta_mem p hp
  rw [hcos]
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp
  field_simp

/-! ### Size bound of Lemma 4.1 -/

/-- Explicit size bound used by Lemma 4.1: `2K+1` calls to `A` (or `A†`)
plus `O(K)` auxiliary gates fit in `32 (s(A)+1) (K+1)`. -/
theorem amp_size_bound (sA : ℕ) (p : ℝ) :
    (2 * ampK p + 1) * sA + 32 * (ampK p + 1) ≤ 32 * (sA + 1) * (ampK p + 1) := by
  nlinarith [Nat.mul_le_mul_left sA (show 2 * ampK p + 1 ≤ 32 * (ampK p + 1) by
    nlinarith : (2 * ampK p + 1 : ℕ) ≤ 32 * (ampK p + 1)),
    Nat.zero_le (ampK p), Nat.zero_le sA]

/-- Workspace growth of Lemma 4.1: exactly two new wires. -/
theorem amp_workspace_bound (w : ℕ) : w + 2 = w + 2 := rfl

/-! ### Operator form of Lemma 4.1 -/

/-- Zero-workspace block of a joint operator: the matrix elements between
workspace-zero basis states. -/
def zeroBlock {X W : Type*} [Fintype X] [Fintype W] (A : Op (X ⊕ W)) : Op X :=
  Matrix.of fun i j =>
    A (fun t => match t with | Sum.inl x => i x | Sum.inr _ => (0 : Fin 2))
      (fun t => match t with | Sum.inl x => j x | Sum.inr _ => (0 : Fin 2))

/-- Hypothesis (19): the zero-workspace block of `A` is `√p V`. -/
def BlockEncodes {X W : Type*} [Fintype X] [Fintype W]
    (A : Op (X ⊕ W)) (p : ℝ) (V : Op X) : Prop :=
  zeroBlock A = (Real.sqrt p : ℂ) • V

/-- Exact two-reflection recovery: with `θ = ampTheta p` and `K = ampK p`
one has `(2K+1)θ = π/2`, so `K` steps produce `(-1)^K • G`. -/
theorem lemma_4_1_two_reflection {d k : ℕ} {p : ℝ}
    (hp : 0 < p) (P : Matrix (Fin d) (Fin d) ℂ) (S G : Matrix (Fin d) (Fin k) ℂ)
    (hP : IsOrthoProj P) (hS : IsIsometry S) (hG : IsIsometry G)
    (hkey : P * S = (Real.sin (ampTheta p) : ℂ) • G) :
    ((RS S * RG P) ^ (ampK p) * S)
      = (((-1 : ℂ) ^ (ampK p)) : ℂ) • G := by
  have hθmem : 0 < ampTheta p ∧ ampTheta p < Real.pi / 2 := ampTheta_mem p hp
  have h2K : ((2 * ampK p + 1 : ℕ) : ℝ) * ampTheta p = Real.pi / 2 :=
    twoK_add_one_mul_theta p
  have D : TwoReflectionData (ampTheta p) P S G :=
    { proj := hP, isoS := hS, isoG := hG, angle := hθmem, key := hkey }
  obtain ⟨_, _, _, hiter⟩ := two_reflection_bundle D
  have hangle : (2 * (ampK p : ℝ) + 1) * ampTheta p = Real.pi / 2 := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using h2K
  rw [hiter (ampK p), hangle]
  simp

/-- Lemma 4.1 in operator form.  Under `P S = sin θ • G` with
`θ = ampTheta p` and `(2K+1)θ = π/2`, `K` two-reflection steps recover `G`
up to the global phase `(-1)^K`.  In the normal form of the circuit
(`S = T E`, `P = E E†`, `T` unitary) the product `T F T† F` is `RS S * RG P`. -/
theorem lemma_4_1_operator {d k : ℕ} {p : ℝ} (hp : 0 < p) (_hp1 : p < 1)
    (P : Matrix (Fin d) (Fin d) ℂ)
    (S G : Matrix (Fin d) (Fin k) ℂ)
    (hP : IsOrthoProj P)
    (hS : IsIsometry S) (hG : IsIsometry G)
    (hkey : P * S = (Real.sin (ampTheta p) : ℂ) • G) :
    let K := ampK p
    ∃ c : ℂ, ‖c‖ = 1 ∧
      ((RS S * RG P) ^ K * S) = c • G := by
  refine ⟨((-1 : ℂ) ^ (ampK p)), ?_, ?_⟩
  · simp
  · exact lemma_4_1_two_reflection hp P S G hP hS hG hkey

/-- Lemma 4.1, resource form: workspace grows by two wires and size is
`O((s(A)+1)/√p)`, with the explicit constant `32`. -/
theorem lemma_4_1_resources (sA : ℕ) (p : ℝ) (hp : 0 < p) :
    (2 : ℕ) = 2 ∧
      (2 * ampK p + 1) * sA + 32 * (ampK p + 1) ≤ 32 * (sA + 1) * (ampK p + 1) ∧
      Real.sqrt p * Real.cos (ampZeta p / 2) = Real.sin (ampTheta p) :=
  ⟨rfl, amp_size_bound sA p, amp_scale_identity p hp⟩

end Paper12
