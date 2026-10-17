import Paper20.Hilbert
import Paper20.Cert
import Mathlib

/-!
# The local BPS expansion and the triangular coefficient system

We use the integer-power version (24) of the defining expansion (1).
If `H ℓ = χ(Hilb^ℓ(C,0))`, then `localBPSExpansion b d H n` says exactly
`(1-q)^b H(q) = ∑_{h=0}^d n_h q^(d-h)(1-q)^(2h)` as a formal series.
There is no choice of a certificate or of a contact polynomial in this definition.
Theorems below derive (25), prove uniqueness, and construct its inverse.
They apply to any integer Hilbert coefficients, independently of formula (13).
-/

namespace Paper20.Semantics

open Finset BigOperators

/-- Coefficient of `q^ℓ` in `(1-q)^b H(q)`. -/
def hilbertResidual (b : ℕ) (H : ℕ → ℤ) (ℓ : ℕ) : ℤ :=
  ∑ i ∈ range (ℓ + 1), (-1 : ℤ)^i * (Nat.choose b i : ℤ) * H (ℓ-i)

/-- Coefficient of `q^ℓ` on the right of (24). -/
def expansionCoeff (d : ℕ) (n : ℕ → ℤ) (ℓ : ℕ) : ℤ :=
  ∑ j ∈ range (d + 1),
    if d-j ≤ ℓ then n j * (-1 : ℤ)^(ℓ-(d-j)) *
      (Nat.choose (2*j) (ℓ-(d-j)) : ℤ) else 0

/-- Equation (1), after clearing `q^(-d)` and substituting
`w = (1-q)^2/q`: equality of every formal-series coefficient (24). -/
def localBPSExpansion (b d : ℕ) (H n : ℕ → ℤ) : Prop :=
  ∀ ℓ, hilbertResidual b H ℓ = expansionCoeff d n ℓ

/-- Equation (25), with no certificate or BPS conclusion assumed. -/
def recurrence25 (d : ℕ) (F n : ℕ → ℤ) : Prop :=
  ∀ h, h ≤ d → n h = F (d-h) -
    ∑ j ∈ Ico (h+1) (d+1), (-1 : ℤ)^(j-h) *
      (Nat.choose (2*j) (j-h) : ℤ) * n j

/-- The triangular structure of the defining BPS expansion. -/
theorem expansionCoeff_triangle (d h : ℕ) (n : ℕ → ℤ) (hh : h ≤ d) :
    expansionCoeff d n (d-h) = n h +
      ∑ j ∈ Ico (h+1) (d+1), (-1 : ℤ)^(j-h) *
        (Nat.choose (2*j) (j-h) : ℤ) * n j := by
  unfold expansionCoeff
  have hcut : (∑ j ∈ range (d+1),
      if d-j ≤ d-h then n j * (-1 : ℤ)^(d-h-(d-j)) *
        (Nat.choose (2*j) (d-h-(d-j)) : ℤ) else 0) =
      ∑ j ∈ Ico h (d+1), n j * (-1 : ℤ)^(j-h) *
        (Nat.choose (2*j) (j-h) : ℤ) := by
    calc
      _ = ∑ j ∈ Ico h (d+1),
          if d-j ≤ d-h then n j * (-1 : ℤ)^(d-h-(d-j)) *
            (Nat.choose (2*j) (d-h-(d-j)) : ℤ) else 0 := by
        symm
        apply Finset.sum_subset
          (by intro j hj; simp only [mem_Ico, mem_range] at *; omega)
        intro j hj hnot
        have hjd : j < d+1 := Finset.mem_range.mp hj
        have hjh : j < h := by simp only [mem_Ico, not_and, not_le] at hnot; omega
        rw [if_neg (by omega)]
      _ = _ := by
        apply sum_congr rfl
        intro j hj
        simp only [mem_Ico] at hj
        rw [if_pos (by omega), show d-h-(d-j) = j-h by omega]
  rw [hcut, Finset.sum_eq_add_sum_diff_singleton (show h ∈ Ico h (d+1) by simp; omega)]
  have hset : Ico h (d+1) \ {h} = Ico (h+1) (d+1) := by
    ext j
    simp only [mem_sdiff, mem_Ico, mem_singleton]
    omega
  rw [hset]
  simp only [Nat.sub_self, pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
  congr 1
  apply sum_congr rfl
  intro j hj
  ring

/-- The defining expansion implies the paper's extraction recurrence. -/
theorem localBPSExpansion_recurrence {b d : ℕ} {H n : ℕ → ℤ}
    (hexp : localBPSExpansion b d H n) : recurrence25 d (hilbertResidual b H) n := by
  intro h hh
  have he := hexp (d-h)
  rw [expansionCoeff_triangle d h n hh] at he
  linarith

/-- The triangular equations have at most one solution on `0,…,d`. -/
theorem recurrence25_unique {d : ℕ} {F n m : ℕ → ℤ}
    (hn : recurrence25 d F n) (hm : recurrence25 d F m) :
    ∀ h, h ≤ d → n h = m h := by
  suffices aux : ∀ t h, d-h = t → h ≤ d → n h = m h from
    fun h hh => aux (d-h) h rfl hh
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro h he hh
    rw [hn h hh, hm h hh]
    congr 1
    apply sum_congr rfl
    intro j hj
    have hj' := Finset.mem_Ico.mp hj
    rw [ih (d-j) (by omega) j rfl (by omega)]

/-- In particular the original BPS defining expansion determines its coefficients. -/
theorem localBPSExpansion_unique {b d : ℕ} {H n m : ℕ → ℤ}
    (hn : localBPSExpansion b d H n) (hm : localBPSExpansion b d H m) :
    ∀ h, h ≤ d → n h = m h :=
  recurrence25_unique (localBPSExpansion_recurrence hn) (localBPSExpansion_recurrence hm)

/-- Coefficients in increasing elimination order, `a_ℓ = n_(d-ℓ)`.
This is structural recursion on `ℓ`; no certificate enters the definition. -/
def inverse (d : ℕ) (F : ℕ → ℤ) (ℓ : ℕ) : ℤ :=
  F ℓ - ∑ t : Fin ℓ,
    (-1 : ℤ)^(ℓ-t.val) * (Nat.choose (2*(d-t.val)) (ℓ-t.val) : ℤ) *
      inverse d F t.val
termination_by ℓ

/-- Canonical coefficients extracted from the lower half of a residual. -/
def extracted (d : ℕ) (F : ℕ → ℤ) (h : ℕ) : ℤ :=
  if h ≤ d then inverse d F (d-h) else 0

/-- The recursively constructed coefficients satisfy (25). -/
theorem extracted_recurrence (d : ℕ) (F : ℕ → ℤ) :
    recurrence25 d F (extracted d F) := by
  intro h hh
  rw [extracted, if_pos hh, inverse]
  congr 1
  apply Finset.sum_bij (fun (t : Fin (d-h)) _ => d-t.val)
  · intro t ht
    simp only [mem_Ico]
    constructor <;> omega
  · intro t ht u hu he
    apply Fin.ext
    omega
  · intro j hj
    have hj' := mem_Ico.mp hj
    refine ⟨⟨d-j, by omega⟩, mem_univ _, ?_⟩
    simp only
    omega
  · intro t ht
    have htd : d-t.val ≤ d := Nat.sub_le _ _
    have hsub : d-(d-t.val) = t.val := by omega
    have hpow : d-h-t.val = d-t.val-h := by omega
    simp only [extracted, if_pos htd, hsub, hpow]

/-- (25) is equivalent to the lower-half coefficients of (24). -/
theorem recurrence25_iff_low (d : ℕ) (F n : ℕ → ℤ) :
    recurrence25 d F n ↔ ∀ ℓ, ℓ ≤ d → F ℓ = expansionCoeff d n ℓ := by
  constructor
  · intro hn ℓ hℓ
    have hh : d-ℓ ≤ d := Nat.sub_le _ _
    have he := hn (d-ℓ) hh
    have hd : d-(d-ℓ) = ℓ := by omega
    have ht := expansionCoeff_triangle d (d-ℓ) n hh
    rw [hd] at he ht
    linarith
  · intro hl h hh
    have he := hl (d-h) (Nat.sub_le _ _)
    rw [expansionCoeff_triangle d h n hh] at he
    linarith

/-- The canonical inverse recovers exactly the coefficients in the original
BPS expansion. No equality to the inverse is an input to this theorem. -/
theorem localBPSExpansion_eq_extracted {b d : ℕ} {H n : ℕ → ℤ}
    (hn : localBPSExpansion b d H n) :
    ∀ h, h ≤ d → n h = extracted d (hilbertResidual b H) h :=
  recurrence25_unique (localBPSExpansion_recurrence hn)
    (extracted_recurrence d (hilbertResidual b H))

/-- The first extraction is the constant residual coefficient. -/
theorem inverse_zero (d : ℕ) (F : ℕ → ℤ) : inverse d F 0 = F 0 := by
  rw [inverse]
  simp

/-- The top BPS coefficient is the constant coefficient of the residual. -/
theorem recurrence25_top {d : ℕ} {F n : ℕ → ℤ}
    (hn : recurrence25 d F n) : n d = F 0 := by
  simpa using hn d le_rfl

end Paper20.Semantics
