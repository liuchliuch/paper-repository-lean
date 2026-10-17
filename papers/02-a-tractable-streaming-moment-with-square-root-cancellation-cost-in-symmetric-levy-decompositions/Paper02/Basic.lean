import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Lebesgue
import Mathlib.Tactic

/-!
# Core definitions for paper 02

Rudin–Shapiro signs, the target moment `f`, second differences `D`,
the symmetric Lévy–Khintchine cone `L_sym`, and the cancellation cost `ρ`.
-/

noncomputable section

namespace Paper02

/-! ## Rudin–Shapiro signs -/

/-- Number of overlapping `11` bit-pairs in the binary expansion of `k`.
Uses fuel-based recursion so concrete values compute definitionally. -/
def adjacentOnesCountAux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | _ + 1, 0 => 0
  | fuel + 1, k + 1 =>
    (if (k + 1) % 4 = 3 then 1 else 0) + adjacentOnesCountAux fuel ((k + 1) / 2)

/-- Number of overlapping `11` bit-pairs in the binary expansion of `k`. -/
def adjacentOnesCount (k : ℕ) : ℕ := adjacentOnesCountAux (k + 1) k

lemma adjacentOnesCount_zero : adjacentOnesCount 0 = 0 := rfl

lemma adjacentOnesCountAux_zero_fuel (k : ℕ) : adjacentOnesCountAux 0 k = 0 := rfl

lemma adjacentOnesCountAux_zero_arg (fuel : ℕ) : adjacentOnesCountAux fuel 0 = 0 := by
  cases fuel with
  | zero => rfl
  | succ f => rfl

lemma adjacentOnesCountAux_succ_succ (fuel k : ℕ) :
    adjacentOnesCountAux (fuel + 1) (k + 1)
      = (if (k + 1) % 4 = 3 then 1 else 0) + adjacentOnesCountAux fuel ((k + 1) / 2) := by
  rfl

lemma adjacentOnesCountAux_of_le (fuel k : ℕ) (h : k ≤ fuel) :
    adjacentOnesCountAux fuel k = adjacentOnesCountAux (fuel + 1) k := by
  induction fuel generalizing k with
  | zero =>
    have hk : k = 0 := by omega
    subst hk
    rw [adjacentOnesCountAux_zero_arg, adjacentOnesCountAux_zero_arg]
  | succ fuel ih =>
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      rw [adjacentOnesCountAux_zero_arg, adjacentOnesCountAux_zero_arg]
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [adjacentOnesCountAux_succ_succ, adjacentOnesCountAux_succ_succ]
      have hdiv : (k' + 1) / 2 ≤ fuel := by omega
      rw [ih _ hdiv]

lemma adjacentOnesCountAux_of_le' (k f1 f2 : ℕ) (h : f1 ≤ f2) (hk : k ≤ f1) :
    adjacentOnesCountAux f1 k = adjacentOnesCountAux f2 k := by
  have step : ∀ d : ℕ, adjacentOnesCountAux f1 k = adjacentOnesCountAux (f1 + d) k := by
    intro d
    induction d with
    | zero => rfl
    | succ d ih =>
      rw [ih]
      exact adjacentOnesCountAux_of_le (f1 + d) k (le_trans hk (Nat.le_add_right f1 d))
  have h' : f2 = f1 + (f2 - f1) := (Nat.add_sub_of_le h).symm
  rw [h']
  exact step (f2 - f1)

lemma adjacentOnesCount_succ (k : ℕ) :
    adjacentOnesCount (k + 1)
      = (if (k + 1) % 4 = 3 then 1 else 0) + adjacentOnesCount ((k + 1) / 2) := by
  unfold adjacentOnesCount
  rw [adjacentOnesCountAux_succ_succ]
  have hle : (k + 1) / 2 + 1 ≤ k + 1 + 1 := by omega
  have hk : (k + 1) / 2 ≤ (k + 1) / 2 + 1 := by omega
  have e : adjacentOnesCountAux (k + 1) ((k + 1) / 2)
      = adjacentOnesCountAux ((k + 1) / 2 + 1) ((k + 1) / 2) := by
    have e1 := adjacentOnesCountAux_of_le' ((k + 1) / 2) ((k + 1) / 2 + 1) (k + 1)
      (by omega) (by omega)
    exact e1.symm
  rw [e]

lemma adjacentOnesCount_one : adjacentOnesCount 1 = 0 := rfl

lemma adjacentOnesCount_two : adjacentOnesCount 2 = 0 := rfl

lemma adjacentOnesCount_three : adjacentOnesCount 3 = 1 := rfl

/-- Rudin–Shapiro sign `r_k = (-1)^{a(k)}` as a real in `{1,-1}`. -/
def rudinShapiro (k : ℕ) : ℝ := (-1 : ℝ) ^ (adjacentOnesCount k)

lemma pow_neg_one_sq (n : ℕ) : ((-1 : ℝ) ^ n) ^ 2 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul]
  simp

lemma rudinShapiro_sq (k : ℕ) : rudinShapiro k ^ 2 = 1 := by
  unfold rudinShapiro
  exact pow_neg_one_sq _

lemma rudinShapiro_mul_self (k : ℕ) : rudinShapiro k * rudinShapiro k = 1 := by
  nlinarith [rudinShapiro_sq k]

lemma rudinShapiro_ne_zero (k : ℕ) : rudinShapiro k ≠ 0 := by
  have := rudinShapiro_sq k
  intro h
  simp [h] at this

lemma abs_rudinShapiro (k : ℕ) : |rudinShapiro k| = 1 := by
  have hsq := rudinShapiro_sq k
  have hle : 0 ≤ rudinShapiro k ∨ rudinShapiro k ≤ 0 := le_total 0 _
  rcases hle with h | h
  · rw [abs_of_nonneg h]; nlinarith
  · rw [abs_of_nonpos h]; nlinarith

lemma rudinShapiro_eq_one_or (k : ℕ) : rudinShapiro k = 1 ∨ rudinShapiro k = -1 := by
  have hsq := rudinShapiro_sq k
  have : (rudinShapiro k - 1) * (rudinShapiro k + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp this with h | h
  · left; linarith
  · right; linarith

lemma rudinShapiro_of_even {k : ℕ} (h : Even (adjacentOnesCount k)) :
    rudinShapiro k = 1 := by
  obtain ⟨m, hm⟩ := h
  unfold rudinShapiro
  rw [hm, ← two_mul, pow_mul]
  simp

lemma rudinShapiro_of_odd {k : ℕ} (h : Odd (adjacentOnesCount k)) :
    rudinShapiro k = -1 := by
  obtain ⟨m, hm⟩ := h
  unfold rudinShapiro
  rw [hm, pow_add, pow_mul]
  simp

lemma rudinShapiro_zero : rudinShapiro 0 = 1 := by
  simp [rudinShapiro, adjacentOnesCount_zero]

lemma rudinShapiro_one : rudinShapiro 1 = 1 := by
  simp [rudinShapiro, adjacentOnesCount_one]

lemma rudinShapiro_two : rudinShapiro 2 = 1 := by
  simp [rudinShapiro, adjacentOnesCount_two]

lemma rudinShapiro_three : rudinShapiro 3 = -1 := by
  simp [rudinShapiro, adjacentOnesCount_three]

/-! ## Target function `f` -/

/-- The paper's fixed even target: `f(0)=0` and `f(k)=2+r_{|k|} ∈ {1,3}` for `k ≠ 0`. -/
def f (k : ℤ) : ℝ :=
  if k = 0 then 0 else 2 + rudinShapiro k.natAbs

lemma f_zero : f 0 = 0 := by
  simp [f]

lemma f_of_ne_zero {k : ℤ} (hk : k ≠ 0) : f k = 2 + rudinShapiro k.natAbs := by
  simp [f, hk]

lemma f_pos {k : ℤ} (hk : k ≠ 0) : 0 < f k := by
  rw [f_of_ne_zero hk]
  rcases rudinShapiro_eq_one_or k.natAbs with h | h <;> simp [h] <;> norm_num

lemma f_nonneg (k : ℤ) : 0 ≤ f k := by
  by_cases hk : k = 0
  · simp [hk, f]
  · exact le_of_lt (f_pos hk)

lemma f_le_three (k : ℤ) : f k ≤ 3 := by
  by_cases hk : k = 0
  · simp [hk, f]
  · rw [f_of_ne_zero hk]
    rcases rudinShapiro_eq_one_or k.natAbs with h | h <;> simp [h] <;> norm_num

lemma f_ge_one_of_ne_zero {k : ℤ} (hk : k ≠ 0) : 1 ≤ f k := by
  rw [f_of_ne_zero hk]
  rcases rudinShapiro_eq_one_or k.natAbs with h | h <;> simp [h] <;> norm_num

lemma f_one : f 1 = 3 := by
  have h : (1:ℤ) ≠ 0 := by norm_num
  rw [f_of_ne_zero h]
  simp [rudinShapiro_one]
  norm_num

lemma f_even (k : ℤ) : f (-k) = f k := by
  by_cases hk : k = 0
  · simp [hk]
  · have hk' : (-k : ℤ) ≠ 0 := by simpa using hk
    rw [f_of_ne_zero hk, f_of_ne_zero hk']
    simp

lemma f_nat (n : ℕ) : f (n : ℤ) = if n = 0 then 0 else 2 + rudinShapiro n := by
  by_cases hn : n = 0
  · simp [hn, f]
  · have hne : (n:ℤ) ≠ 0 := by simpa using hn
    rw [f_of_ne_zero hne]
    simp [hn]

lemma f_nat_of_ne_zero {n : ℕ} (hn : n ≠ 0) : f (n : ℤ) = 2 + rudinShapiro n := by
  rw [f_nat, if_neg hn]

lemma f_ne_zero_of_ne_zero {k : ℤ} (hk : k ≠ 0) : f k ≠ 0 :=
  ne_of_gt (f_pos hk)

/-! ## Second differences -/

/-- Centered second difference `D u(k) = (u(k+1)-2u(k)+u(k-1))/2`. -/
noncomputable def secondDiff (u : ℤ → ℝ) (k : ℤ) : ℝ :=
  (u (k + 1) - 2 * u k + u (k - 1)) / 2

lemma secondDiff_eq (u : ℤ → ℝ) (k : ℤ) :
    secondDiff u k = (u (k + 1) - 2 * u k + u (k - 1)) / 2 := rfl

lemma secondDiff_two_mul (u : ℤ → ℝ) (k : ℤ) :
    2 * secondDiff u k = u (k + 1) - 2 * u k + u (k - 1) := by
  rw [secondDiff_eq]; ring

lemma secondDiff_gaussian (A : ℝ) (k : ℤ) :
    secondDiff (fun x => A * (x : ℝ) ^ 2) k = A := by
  rw [secondDiff_eq]
  have e1 : ((k : ℝ) + 1) ^ 2 = (k : ℝ) ^ 2 + 2 * (k : ℝ) + 1 := by ring
  have e2 : ((k : ℝ) - 1) ^ 2 = (k : ℝ) ^ 2 - 2 * (k : ℝ) + 1 := by ring
  have c1 : (((k : ℤ) + 1 : ℤ) : ℝ) = (k : ℝ) + 1 := by simp
  have c2 : (((k : ℤ) - 1 : ℤ) : ℝ) = (k : ℝ) - 1 := by simp
  rw [c1, c2, e1, e2]
  ring

lemma secondDiff_const (c : ℝ) (k : ℤ) :
    secondDiff (fun _ => c) k = 0 := by
  rw [secondDiff_eq]
  ring

lemma secondDiff_cos (s : ℝ) (k : ℤ) :
    secondDiff (fun x : ℤ => 1 - Real.cos ((x : ℝ) * s)) k
      = (1 - Real.cos s) * Real.cos ((k : ℝ) * s) := by
  rw [secondDiff_eq]
  have c1 : (((k : ℤ) + 1 : ℤ) : ℝ) = (k : ℝ) + 1 := by simp
  have c2 : (((k : ℤ) - 1 : ℤ) : ℝ) = (k : ℝ) - 1 := by simp
  rw [c1, c2]
  have key : Real.cos (((k : ℝ) + 1) * s) + Real.cos (((k : ℝ) - 1) * s)
      = 2 * Real.cos ((k : ℝ) * s) * Real.cos s := by
    have e1 : ((k : ℝ) + 1) * s = (k : ℝ) * s + s := by ring
    have e2 : ((k : ℝ) - 1) * s = (k : ℝ) * s - s := by ring
    rw [e1, e2, Real.cos_add, Real.cos_sub]
    ring
  have hnum :
      (1 - Real.cos (((k : ℝ) + 1) * s) - 2 * (1 - Real.cos ((k : ℝ) * s))
          + (1 - Real.cos (((k : ℝ) - 1) * s)))
        = 2 * Real.cos ((k : ℝ) * s) - Real.cos (((k : ℝ) + 1) * s)
            - Real.cos (((k : ℝ) - 1) * s) := by
    ring
  have hrearr :
      2 * Real.cos ((k : ℝ) * s) - Real.cos (((k : ℝ) + 1) * s)
          - Real.cos (((k : ℝ) - 1) * s)
        = 2 * Real.cos ((k : ℝ) * s)
            - (Real.cos (((k : ℝ) + 1) * s) + Real.cos (((k : ℝ) - 1) * s)) := by
    ring
  rw [hnum, hrearr, key]
  ring

lemma secondDiff_add (u v : ℤ → ℝ) (k : ℤ) :
    secondDiff (fun x => u x + v x) k = secondDiff u k + secondDiff v k := by
  simp only [secondDiff_eq]
  ring

lemma secondDiff_neg (u : ℤ → ℝ) (k : ℤ) :
    secondDiff (fun x => - u x) k = - secondDiff u k := by
  simp only [secondDiff_eq]
  ring

lemma secondDiff_sub (u v : ℤ → ℝ) (k : ℤ) :
    secondDiff (fun x => u x - v x) k = secondDiff u k - secondDiff v k := by
  simp only [secondDiff_eq]
  ring

lemma secondDiff_smul (c : ℝ) (u : ℤ → ℝ) (k : ℤ) :
    secondDiff (fun x => c * u x) k = c * secondDiff u k := by
  simp only [secondDiff_eq]
  ring

/-! ## Symmetric Lévy–Khintchine cone -/

open MeasureTheory

/-- Lévy-measure integrability: `∫ min(s²,1) dν < ∞`. -/
def LevyIntegrable (ν : Measure ℝ) : Prop :=
  MeasureTheory.lintegral ν (fun s : ℝ => ENNReal.ofReal (min (s^2) 1)) < ⊤

/-- Certificate that `g` is a symmetric Lévy–Khintchine exponent. -/
structure LSymCert (g : ℝ → ℝ) where
  A : ℝ
  A_nonneg : 0 ≤ A
  ν : Measure ℝ
  ν_pos : 0 ≤ ν
  ν_support : ν.restrict (Set.Iic (0:ℝ)) = 0
  ν_integrable : LevyIntegrable ν
  apply_eq : ∀ x : ℝ,
    g x = A * x^2 + ∫ s in Set.Ioi (0:ℝ), (1 - Real.cos (x * s)) ∂ν

/-- Membership in the cone `L_sym`. -/
def IsLSym (g : ℝ → ℝ) : Prop := Nonempty (LSymCert g)

/-- Gaussian exponents `x ↦ A x²` with `A ≥ 0` belong to `L_sym`. -/
def gaussianCert (A : ℝ) (hA : 0 ≤ A) : LSymCert (fun x => A * x ^ 2) where
  A := A
  A_nonneg := hA
  ν := 0
  ν_pos := le_refl 0
  ν_support := by simp
  ν_integrable := by
    show MeasureTheory.lintegral (0 : Measure ℝ) _ < ⊤
    simp
  apply_eq := by
    intro x
    simp

lemma isLSym_gaussian {A : ℝ} (hA : 0 ≤ A) : IsLSym (fun x => A * x ^ 2) :=
  ⟨gaussianCert A hA⟩

/-- Atomic jump exponent `x ↦ ∑ i, c_i (1 - cos(x s_i))` with `c_i ≥ 0`, `s_i > 0`. -/
def atomicLSym {n : ℕ} (s : Fin n → ℝ) (hs : ∀ i, 0 < s i)
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) : ℝ → ℝ :=
  fun x => ∑ i, c i * (1 - Real.cos (x * s i))

/-! ## Cancellation cost `ρ` -/

/-- Approximate split of `f` on `[-n,n]` with cancellation envelope `ρ f`. -/
def AdmissibleSplit (gpos gneg : ℤ → ℝ) (f : ℤ → ℝ) (n : ℕ) (η ρ : ℝ) : Prop :=
  (∀ k : ℤ, |k| ≤ n → |gpos k - gneg k - f k| ≤ η * f k) ∧
  (∀ k : ℤ, |k| ≤ n → gpos k + gneg k ≤ ρ * f k)

/-- Integer restriction of a real symmetric exponent. -/
def RestrictInt (g : ℝ → ℝ) : ℤ → ℝ := fun k => g (k : ℝ)

/-- Admissible pair coming from integer restrictions of `L_sym` functions. -/
def AdmissibleLSymPair (gpos gneg : ℝ → ℝ) (f : ℤ → ℝ) (n : ℕ) (η ρ : ℝ) : Prop :=
  IsLSym gpos ∧ IsLSym gneg ∧
  AdmissibleSplit (RestrictInt gpos) (RestrictInt gneg) f n η ρ

/-- Paper cancellation cost `ρ_η^f(n)`: infimum of admissible `ρ ≥ 0`. -/
noncomputable def rho (f : ℤ → ℝ) (n : ℕ) (η : ℝ) : ℝ :=
  sInf {ρ | 0 ≤ ρ ∧ ∃ gpos gneg : ℝ → ℝ, AdmissibleLSymPair gpos gneg f n η ρ}

lemma rhoSet_of_pair {f : ℤ → ℝ} {n : ℕ} {η ρ : ℝ} {gpos gneg : ℝ → ℝ}
    (hρ : 0 ≤ ρ) (h : AdmissibleLSymPair gpos gneg f n η ρ) :
    ρ ∈ {ρ | 0 ≤ ρ ∧ ∃ gpos gneg : ℝ → ℝ, AdmissibleLSymPair gpos gneg f n η ρ} :=
  ⟨hρ, gpos, gneg, h⟩

lemma rho_le_of_pair {f : ℤ → ℝ} {n : ℕ} {η ρ : ℝ} {gpos gneg : ℝ → ℝ}
    (hρ : 0 ≤ ρ) (h : AdmissibleLSymPair gpos gneg f n η ρ)
    (hne : (∃ gpos gneg : ℝ → ℝ, AdmissibleLSymPair gpos gneg f n η ρ)) :
    rho f n η ≤ ρ :=
  csInf_le ⟨0, fun x hx => hx.1⟩ (rhoSet_of_pair hρ h)

end Paper02
