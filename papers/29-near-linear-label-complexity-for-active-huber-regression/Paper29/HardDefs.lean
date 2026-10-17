import Paper29.Defs
import Paper29.InformationDefs

/-! Definitions of the fixed hard designs and the finite hard response laws. -/
noncomputable section
open scoped BigOperators
namespace Paper29.HardDistribution

abbrev Signs (r : ℕ) := Fin r → Bool
abbrev Bits (r N : ℕ) := Fin r × Fin N → Bool

def sign (b : Bool) : ℝ := if b then 1 else -1

def bit (b : Bool) : ℝ := if b then 1 else 0

def bitMass (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

def beta (ε : ℝ) (N : ℕ) : ℝ := max (200 * ε) (Real.sqrt (10 / (N : ℝ)))

/-- Restriction to the first r ambient coordinates. -/
def embedding (r d : ℕ) : Matrix (Fin r) (Fin d) ℝ :=
  fun j k => if j.val = k.val then 1 else 0

/-- The standard basis rows followed by zero rows. -/
def shortCore (n r : ℕ) : Matrix (Fin n) (Fin r) ℝ :=
  fun i j => if i.val = j.val then 1 else 0

/-- N consecutive copies of 4 e_j for each j, followed by zero rows. -/
def longCore (n r N : ℕ) : Matrix (Fin n) (Fin r) ℝ :=
  fun i j => if i.val / N = j.val ∧ i.val < r * N then 4 else 0

def shortDesign (n d r : ℕ) : Matrix (Fin n) (Fin d) ℝ :=
  shortCore n r * embedding r d

def longDesign (n d r N : ℕ) : Matrix (Fin n) (Fin d) ℝ :=
  longCore n r N * embedding r d

/-- One fixed design for every admissible n,d,r, with the paper's two regimes. -/
def fixedDesign (n d r : ℕ) : Matrix (Fin n) (Fin d) ℝ :=
  if n / r < 160 then shortDesign n d r else longDesign n d r (n / r)

/-- Independent uniform signs, written as a finite mass function. -/
def signMass (r : ℕ) (_s : Signs r) : ℝ := ((2 : ℝ) ^ r)⁻¹

/-- Conditional product Bernoulli response law, given all hidden signs. -/
def conditionalMass {r N : ℕ} (β : ℝ) (s : Signs r) (y : Bits r N) : ℝ :=
  ∏ a, bitMass (1 / 2 + β * sign (s a.1)) (y a)

/-- Genuine finite joint mass of the hidden signs and all response bits. -/
def hardMass {r N : ℕ} (β : ℝ) (s : Signs r) (y : Bits r N) : ℝ :=
  signMass r s * conditionalMass β s y

/-- Short-regime response, with the unused rows exactly zero. -/
def shortResponse {n r : ℕ} (s : Signs r) (i : Fin n) : ℝ :=
  if hi : i.val < r then sign (s ⟨i.val, hi⟩) else 0

/-- Long-regime response, including the fewer than r padding rows. -/
def longResponse {n r N : ℕ} (y : Bits r N) (i : Fin n) : ℝ :=
  if hi : i.val < r * N then
    if hN : 0 < N then
      4 * bit (y (⟨i.val / N, (Nat.div_lt_iff_lt_mul hN).2 hi⟩,
        ⟨i.val % N, Nat.mod_lt _ hN⟩))
    else 0
  else 0

def blockMean {r N : ℕ} (y : Bits r N) (j : Fin r) : ℝ :=
  (∑ k, bit (y (j, k))) / N

def GoodBlock {r N : ℕ} (β : ℝ) (s : Signs r) (y : Bits r N) (j : Fin r) : Prop :=
  β / 2 ≤ sign (s j) * (blockMean y j - 1 / 2)

end Paper29.HardDistribution
