import Mathlib
import Paper20.Hilbert

/-!
# Polynomial model of §3 (contact order)

`D_a(w)` from (16)–(17), `A_{λ,j}(u)` from (19), `R_λ(w)` from (28)–(29),
and the contact-order polynomials `Q_{r,h}(u)` from (20).

Self-contained over `List ℚ` (low degree first); does not depend on
`Paper20.Hilbert`.  Certificate arrays for `r = 36` live in `Paper20.Certs.Q36`.

Proved here:
* recurrence (17) and `D_a(0) = a` (odd) / `a/2` (even);
* `A_{λ,j}` has degree at most `j` and `[u^j] A_{λ,j} = (c²)^j / (2j)!`;
* `R_λ(0) = 1` from (29);
* `Q_{r,h}` of (20) has degree at most `h`;
* The spectral-sum form of Proposition 3.2; the identification with actual transposition-walk counts is still required;
* the necessary leading-coefficient test (23).

Remaining obligations, retained as explicit hypotheses in conditional lemmas:
* `dimSquareSum r = r!` (sum of squares of irreducible degrees of `S_r`);
* vanishing of `Q_{r,h}(0)` for `h > 0`, from `B_{r,0} = τ(Ω) = 1`;
* the series identity (21) ⇒ (20) identifying `n_h(C_{r,k})` with `Q_{r,h}(k(k+1))`.
-/

namespace Paper20

/-! ## Truncated polynomials over `ℚ` (low degree first) -/

/-- Coefficient of `x^i`, or `0` out of range. -/
def cget (cs : List ℚ) (i : ℕ) : ℚ := cs.getD i 0

@[simp] theorem cget_nil (i : ℕ) : cget ([] : List ℚ) i = 0 := rfl

@[simp] theorem cget_cons_zero (x : ℚ) (xs : List ℚ) : cget (x :: xs) 0 = x := rfl

@[simp] theorem cget_cons_succ (x : ℚ) (xs : List ℚ) (i : ℕ) :
    cget (x :: xs) (i + 1) = cget xs i := rfl

theorem cget_of_length_le {cs : List ℚ} {i : ℕ} (h : cs.length ≤ i) : cget cs i = 0 :=
  List.getD_eq_default cs 0 h

/-- Polynomial addition. -/
def padd : List ℚ → List ℚ → List ℚ
  | [], b => b
  | a, [] => a
  | x :: xs, y :: ys => (x + y) :: padd xs ys

/-- Scalar multiplication. -/
def psmul (s : ℚ) : List ℚ → List ℚ
  | [] => []
  | x :: xs => s * x :: psmul s xs

/-- Polynomial product as a convolution (low degree first). -/
def pmul (a b : List ℚ) : List ℚ :=
  (List.range (a.length + b.length)).map fun k =>
    ((List.range (k + 1)).map fun i => cget a i * cget b (k - i)).sum

theorem cget_padd : ∀ (a b : List ℚ) (i : ℕ), cget (padd a b) i = cget a i + cget b i
  | [], b, i => by simp [padd]
  | a, [], i => by cases a with
    | nil => simp [padd]
    | cons x xs => simp [padd]
  | x :: xs, y :: ys, 0 => by simp [padd]
  | x :: xs, y :: ys, i + 1 => by
    have := cget_padd xs ys i
    simpa [padd] using this

theorem cget_psmul (s : ℚ) : ∀ (a : List ℚ) (i : ℕ), cget (psmul s a) i = s * cget a i
  | [], i => by simp [psmul]
  | x :: xs, 0 => by simp [psmul]
  | x :: xs, i + 1 => by
    have := cget_psmul s xs i
    simpa [psmul] using this

theorem length_pmul (a b : List ℚ) :
    (pmul a b).length = a.length + b.length := by
  unfold pmul
  rw [List.length_map, List.length_range]

theorem cget_pmul_of_lt (a b : List ℚ) {k : ℕ} (h : a.length + b.length ≤ k) :
    cget (pmul a b) k = 0 := by
  apply cget_of_length_le
  rw [length_pmul]
  exact h

/-- Coefficient formula for `pmul` (Cauchy convolution). -/
theorem cget_pmul (a b : List ℚ) (k : ℕ) :
    cget (pmul a b) k = ((List.range (k + 1)).map fun i => cget a i * cget b (k - i)).sum := by
  unfold cget pmul
  rw [List.getD_eq_getD_getElem?, List.getElem?_map]
  by_cases h : k < a.length + b.length
  · rw [List.getElem?_range h, Option.map_some, Option.getD_some]
    simp only [cget]
  · have hn : (List.range (a.length + b.length))[k]? = none := by
      rw [List.getElem?_eq_none]
      rw [List.length_range]
      omega
    rw [hn, Option.map_none, Option.getD_none]
    have hsum : ((List.range (k + 1)).map fun i =>
        a.getD i 0 * b.getD (k - i) 0).sum = (0 : ℚ) := by
      apply List.sum_eq_zero
      intro t ht
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
      have hi' : i ≤ k := by
        have := List.mem_range.mp hi
        omega
      by_cases ha : a.length ≤ i
      · rw [List.getD_eq_default a 0 ha, zero_mul]
      · by_cases hb : b.length ≤ k - i
        · rw [List.getD_eq_default b 0 hb, mul_zero]
        · push_neg at ha hb
          have : i + (k - i) < a.length + b.length := Nat.add_lt_add ha hb
          omega
    exact hsum.symm

/-- Evaluation at `x` by Horner's rule. -/
def peval (cs : List ℚ) (x : ℚ) : ℚ :=
  match cs with
  | [] => 0
  | c :: rest => c + x * peval rest x

@[simp] theorem peval_nil (x : ℚ) : peval ([] : List ℚ) x = 0 := rfl

@[simp] theorem peval_cons (c : ℚ) (rest : List ℚ) (x : ℚ) :
    peval (c :: rest) x = c + x * peval rest x := rfl

theorem peval_zero (cs : List ℚ) : peval cs 0 = cget cs 0 := by
  induction cs with
  | nil => rfl
  | cons y ys ih =>
    simp [ih]

/-! ## Quantum integers `D_a(w)` — equations (16)–(17) -/

/-- Coefficients of `D_a(w)`, low degree first (17). `D_0 = [1]` is unused. -/
def Dpoly : ℕ → List ℚ
  | 0 => [1]
  | 1 => [1]
  | 2 => [1]
  | 3 => [3, 1]
  | 4 => [2, 1]
  | n + 5 => padd (pmul [2, 1] (Dpoly (n + 3))) (psmul (-1) (Dpoly (n + 1)))

/-- Constant term `D_a(0)` from (17). -/
def Dconst (a : ℕ) : ℚ := cget (Dpoly a) 0

@[simp] theorem Dpoly_zero : Dpoly 0 = [1] := rfl
@[simp] theorem Dpoly_one : Dpoly 1 = [1] := rfl
@[simp] theorem Dpoly_two : Dpoly 2 = [1] := rfl
@[simp] theorem Dpoly_three : Dpoly 3 = [3, 1] := rfl
@[simp] theorem Dpoly_four : Dpoly 4 = [2, 1] := rfl

/-- Recurrence (17) for `a ≥ 5`. -/
theorem Dpoly_rec (a : ℕ) (h : 5 ≤ a) :
    Dpoly a = padd (pmul [2, 1] (Dpoly (a - 2))) (psmul (-1) (Dpoly (a - 4))) := by
  obtain ⟨n, rfl⟩ : ∃ n, a = n + 5 := ⟨a - 5, by omega⟩
  have h2 : n + 5 - 2 = n + 3 := by omega
  have h4 : n + 5 - 4 = n + 1 := by omega
  simp only [Dpoly, h2, h4]

theorem cget_Dpoly_zero : ∀ (a : ℕ), 1 ≤ a →
    cget (Dpoly a) 0 = if a % 2 = 1 then (a : ℚ) else (a : ℚ) / 2 := by
  intro a
  refine Nat.strongRecOn a ?_
  intro a ih ha
  rcases a with _ | _ | _ | _ | _ | n
  · exact absurd ha (by omega : ¬(1 ≤ 0))
  · norm_num [Dpoly]
  · norm_num [Dpoly]
  · norm_num [Dpoly]
  · norm_num [Dpoly]
  · have h2 : n + 5 - 2 = n + 3 := by omega
    have h4 : n + 5 - 4 = n + 1 := by omega
    have ih3 : cget (Dpoly (n + 3)) 0 = if (n + 3) % 2 = 1 then ((n + 3 : ℕ) : ℚ)
        else ((n + 3 : ℕ) : ℚ) / 2 := ih (n + 3) (by omega) (by omega)
    have ih1 : cget (Dpoly (n + 1)) 0 = if (n + 1) % 2 = 1 then ((n + 1 : ℕ) : ℚ)
        else ((n + 1 : ℕ) : ℚ) / 2 := ih (n + 1) (by omega) (by omega)
    rw [Dpoly_rec (n + 5) (by omega), h2, h4, cget_padd, cget_psmul]
    have hpmul : cget (pmul [2, 1] (Dpoly (n + 3))) 0
        = (2 : ℚ) * cget (Dpoly (n + 3)) 0 := by
      rw [cget_pmul]
      have hsum :
          ((List.range (0 + 1)).map fun i =>
            cget [2, 1] i * cget (Dpoly (n + 3)) (0 - i)).sum
          = (2 : ℚ) * cget (Dpoly (n + 3)) 0 := by
        simp [cget]
      exact hsum
    rw [hpmul]
    by_cases hp : (n + 5) % 2 = 1
    · have e3 : (n + 3) % 2 = 1 := by omega
      have e1 : (n + 1) % 2 = 1 := by omega
      rw [ih3, if_pos e3, ih1, if_pos e1, if_pos hp]
      push_cast
      ring
    · have e3 : (n + 3) % 2 ≠ 1 := by omega
      have e1 : (n + 1) % 2 ≠ 1 := by omega
      rw [ih3, if_neg e3, ih1, if_neg e1, if_neg hp]
      push_cast
      field_simp
      ring

/-- `D_a(0) = a` for odd `a ≥ 1` (17). -/
theorem Dconst_odd (a : ℕ) (h : Odd a) : Dconst a = a := by
  have e : a % 2 = 1 := Nat.odd_iff.mp h
  have ha : 1 ≤ a := by
    obtain ⟨k, rfl⟩ := h
    omega
  unfold Dconst
  rw [cget_Dpoly_zero a ha, if_pos e]

/-- `D_a(0) = a/2` for even `a ≥ 2` (17). -/
theorem Dconst_even {a : ℕ} (h : Even a) (ha : 2 ≤ a) : Dconst a = ((a / 2 : ℕ) : ℚ) := by
  have e : a % 2 = 0 := Nat.even_iff.mp h
  have ha1 : 1 ≤ a := by omega
  unfold Dconst
  rw [cget_Dpoly_zero a ha1, if_neg (by omega)]
  have hmul : ((a / 2 : ℕ) : ℚ) * 2 = (a : ℚ) := by
    have ha2 : a = 2 * (a / 2) := by
      have h1 : 2 * (a / 2) + a % 2 = a := Nat.div_add_mod a 2
      omega
    conv_rhs => rw [ha2]
    push_cast
    ring
  rw [div_eq_iff (by norm_num : (2 : ℚ) ≠ 0)]
  exact hmul.symm

theorem Dconst_pos (a : ℕ) (h : 1 ≤ a) : 0 < Dconst a := by
  by_cases ho : Odd a
  · rw [Dconst_odd a ho]
    exact_mod_cast h
  · have he : Even a := by
      rcases Nat.even_or_odd a with he | ho'
      · exact he
      · exact absurd ho' ho
    have ha2 : 2 ≤ a := by
      rcases a with _ | _ | n
      · omega
      · exact absurd (Nat.odd_iff.mpr (by norm_num : (1 : ℕ) % 2 = 1)) ho
      · omega
    rw [Dconst_even he ha2]
    have ha : 1 ≤ (a / 2 : ℕ) := by
      have : a % 2 = 0 := Nat.even_iff.mp he
      omega
    exact_mod_cast ha

theorem Dconst_ne_zero (a : ℕ) (h : 1 ≤ a) : Dconst a ≠ 0 :=
  ne_of_gt (Dconst_pos a h)

/-! ## Content polynomials `A_{λ,j}(u)` — equation (19) -/

/-- The parameter `t` of (19): `2(j-1)` if `c` even, `2j-1` if `c` odd. -/
def At (cEven : Bool) (j : ℕ) : ℕ := if cEven then 2 * (j - 1) else 2 * j - 1

/-- Linear factor `(c²(4u+1) - t²) / (4(2j)(2j-1))` of (19), as `[k0, k1]`. -/
def Afactor (c2 : ℤ) (cEven : Bool) (j : ℕ) : List ℚ :=
  let den : ℚ := ((4 * (2 * j) * (2 * j - 1) : ℕ) : ℚ)
  let t : ℕ := At cEven j
  [((c2 - (t * t : ℕ) : ℤ) : ℚ) / den, ((4 * c2 : ℤ) : ℚ) / den]

theorem Afactor_length (c2 : ℤ) (cEven : Bool) (j : ℕ) :
    (Afactor c2 cEven j).length = 2 := rfl

theorem cget_Afactor_zero (c2 : ℤ) (cEven : Bool) (j : ℕ) :
    cget (Afactor c2 cEven j) 0
      = ((c2 - ((At cEven j * At cEven j : ℕ) : ℤ) : ℤ) : ℚ)
        / ((4 * (2 * j) * (2 * j - 1) : ℕ) : ℚ) := rfl

theorem cget_Afactor_one (c2 : ℤ) (cEven : Bool) (j : ℕ) :
    cget (Afactor c2 cEven j) 1
      = ((4 * c2 : ℤ) : ℚ) / ((4 * (2 * j) * (2 * j - 1) : ℕ) : ℚ) := rfl

theorem cget_Afactor_ge_two (c2 : ℤ) (cEven : Bool) (j i : ℕ) (h : 2 ≤ i) :
    cget (Afactor c2 cEven j) i = 0 := by
  have : (Afactor c2 cEven j).length = 2 := Afactor_length _ _ _
  exact cget_of_length_le (by rw [this]; omega)

/-- `A_{λ,j}(u)` depends only on `c²` and the parity of `c`. -/
def Apoly (c2 : ℤ) (cEven : Bool) : ℕ → List ℚ
  | 0 => [1]
  | j + 1 => pmul (Apoly c2 cEven j) (Afactor c2 cEven (j + 1))

@[simp] theorem Apoly_zero (c2 : ℤ) (cEven : Bool) : Apoly c2 cEven 0 = [1] := rfl

theorem Apoly_succ (c2 : ℤ) (cEven : Bool) (j : ℕ) :
    Apoly c2 cEven (j + 1) = pmul (Apoly c2 cEven j) (Afactor c2 cEven (j + 1)) := rfl

/-- Degree bound of (19): `A_{λ,j}` has degree at most `j`. -/
theorem cget_Apoly_of_lt {c2 : ℤ} {cEven : Bool} {i j : ℕ} (h : j < i) :
    cget (Apoly c2 cEven j) i = 0 := by
  induction j generalizing i with
  | zero =>
    have : (Apoly c2 cEven 0).length = 1 := rfl
    exact cget_of_length_le (by rw [this]; omega)
  | succ j ih =>
    -- `cget A_{j+1} i = 0` for `j+1 < i`
    rw [Apoly_succ, cget_pmul]
    apply List.sum_eq_zero
    intro t ht
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp ht
    have hm' : m ≤ i := by
      have := List.mem_range.mp hm
      omega
    by_cases hkj : m ≤ j
    · have hA : cget (Afactor c2 cEven (j + 1)) (i - m) = 0 :=
        cget_Afactor_ge_two c2 cEven (j + 1) (i - m) (by omega)
      rw [hA, mul_zero]
    · have : cget (Apoly c2 cEven j) m = 0 := ih (by omega)
      rw [this, zero_mul]

/-- Leading coefficient of `A_{λ,j}` (key step of Proposition 3.2):
    `[u^j] A_{λ,j} = (c²)^j / (2j)!`. -/
theorem cget_Apoly_self (c2 : ℤ) (cEven : Bool) (j : ℕ) :
    cget (Apoly c2 cEven j) j = ((c2 ^ j : ℤ) : ℚ) / (((2 * j).factorial : ℕ) : ℚ) := by
  induction j with
  | zero => norm_num [Apoly, cget]
  | succ j ih =>
    rw [Apoly_succ, cget_pmul]
    -- Only `i = j` contributes to the coefficient of `u^{j+1}`.
    have hsum :
        ((List.range (j + 1 + 1)).map fun i =>
          cget (Apoly c2 cEven j) i * cget (Afactor c2 cEven (j + 1)) (j + 1 - i)).sum
        = cget (Apoly c2 cEven j) j * cget (Afactor c2 cEven (j + 1)) 1 := by
      have hsplit' : List.range (j + 2) = List.range j ++ [j, j + 1] := by
        rw [List.range_succ, List.range_succ, List.append_assoc]
        rfl
      rw [hsplit', List.map_append, List.sum_append]
      have hmid :
          ((List.range j).map fun i =>
            cget (Apoly c2 cEven j) i * cget (Afactor c2 cEven (j + 1)) (j + 1 - i)).sum = 0 := by
        apply List.sum_eq_zero
        intro t ht
        obtain ⟨m, hm, rfl⟩ := List.mem_map.mp ht
        have hm' : m < j := List.mem_range.mp hm
        have hA : cget (Afactor c2 cEven (j + 1)) (j + 1 - m) = 0 :=
          cget_Afactor_ge_two c2 cEven (j + 1) (j + 1 - m) (by omega)
        rw [hA, mul_zero]
      have hlast :
          (([j, j + 1]).map fun i =>
            cget (Apoly c2 cEven j) i * cget (Afactor c2 cEven (j + 1)) (j + 1 - i)).sum
          = cget (Apoly c2 cEven j) j * cget (Afactor c2 cEven (j + 1)) 1
            + cget (Apoly c2 cEven j) (j + 1) * cget (Afactor c2 cEven (j + 1)) 0 := by
        norm_num [Nat.add_sub_cancel_left, Nat.add_sub_cancel]
      have htop : cget (Apoly c2 cEven j) (j + 1) = 0 := cget_Apoly_of_lt (by omega)
      rw [hmid, hlast, htop, zero_mul]
      abel
    rw [hsum, ih]
    have hf : cget (Afactor c2 cEven (j + 1)) 1
        = ((4 * c2 : ℤ) : ℚ) / ((4 * (2 * (j + 1)) * (2 * (j + 1) - 1) : ℕ) : ℚ) :=
      cget_Afactor_one _ _ _
    rw [hf]
    -- Arithmetic: `c2^j / (2j)! * 4c2 / (4(2j+2)(2j+1)) = c2^{j+1} / (2j+2)!`
    have e1 : (2 * (j + 1) : ℕ) = 2 * j + 2 := by ring
    have e2 : (2 * j + 2 - 1 : ℕ) = 2 * j + 1 := rfl
    have hpow : ((c2 ^ (j + 1) : ℤ) : ℚ) = ((c2 ^ j : ℤ) : ℚ) * ((c2 : ℤ) : ℚ) := by
      rw [pow_succ, Int.cast_mul]
    rw [e1, e2, hpow]
    have hfac : ((2 * j + 2).factorial : ℕ) = (2 * j + 2) * (2 * j + 1) * (2 * j).factorial := by
      rw [Nat.factorial_succ, Nat.factorial_succ]
      ring
    have h4 : ((4 * (2 * j + 2) * (2 * j + 1) : ℕ) : ℚ)
        = (4 : ℚ) * (2 * j + 2) * (2 * j + 1) := by
      push_cast
      ring
    rw [h4, hfac]
    push_cast
    field_simp
    try ring

/-! ## Partitions (self-contained model of Appendix A) -/

/-- Hook lengths of a part-list (zero-based rows and columns). -/
def partsHooks (parts : List ℕ) : List ℕ :=
  (parts.zipIdx).flatMap fun (a, i) =>
    (List.range a).map fun j =>
      a - j + ((parts.filter (· > j)).length) - i - 1

/-- Content `c = Σ (j - i)` over boxes. -/
def partsContent (parts : List ℕ) : ℤ :=
  (parts.zipIdx).foldl (fun acc (a, i) =>
    acc + ((a * (a - 1) / 2 : ℕ) : ℤ) - ((i * a : ℕ) : ℤ)) 0

/-- Hook-length dimension `f^λ = r! / Π hooks`. -/
def partsDim (r : ℕ) (parts : List ℕ) : ℕ :=
  r.factorial / (partsHooks parts).prod

/-- Number of even hook lengths. -/
def partsEvenHooks (parts : List ℕ) : ℕ :=
  (partsHooks parts).countP (fun a => a % 2 = 0)

/-! ## Series `R_λ` from (28)–(29) -/

/-- Coefficients `g_0, …, g_{H-1}` of the formal series `-D'/D`. -/
def negDLog (D : List ℚ) : (H : ℕ) → List ℚ
  | 0 => []
  | H + 1 =>
    let prev := negDLog D H
    let j := H
    let d0 := D.getD 0 0
    let s := ((List.range j).map fun t => D.getD (t + 1) 0 * prev.getD (j - 1 - t) 0).sum
    prev ++ [((-(j + 1 : ℚ) * D.getD (j + 1) 0 - s) / d0)]

/-- Logarithmic-derivative coefficients `γ_j` of `R_λ` (28), length `H+1`. -/
def gammaSeries (hooks : List ℕ) (eEven : ℕ) (H : ℕ) : List ℚ :=
  (List.range (H + 1)).map fun j =>
    if j = 0 then (0 : ℚ)
    else
      let gsum := hooks.foldl (fun acc a => acc + (negDLog (Dpoly a) H).getD (j - 1) 0) 0
      gsum + (((eEven / 2 : ℕ) : ℚ) * (if j % 2 = 0 then (1 : ℚ) else -1)
        / ((4 ^ j : ℕ) : ℚ))

/-- Coefficients `r_0, …, r_H` from (29), with `r_0 = 1`. -/
def rFromGamma (γ : List ℚ) : (H : ℕ) → List ℚ
  | 0 => [1]
  | H + 1 =>
    let prev := rFromGamma γ H
    let m := H + 1
    let s := ((List.range m).map fun i => γ.getD (i + 1) 0 * prev.getD (m - 1 - i) 0).sum
    prev ++ [s / m]

/-- `R_λ(w)` truncated to degree `H`, from (28)–(29). -/
def Rseries (hooks : List ℕ) (eEven : ℕ) (H : ℕ) : List ℚ :=
  rFromGamma (gammaSeries hooks eEven H) H


theorem length_rFromGamma (γ : List ℚ) (H : ℕ) : 1 ≤ (rFromGamma γ H).length := by
  induction H with
  | zero => simp [rFromGamma]
  | succ H ih =>
    simp only [rFromGamma, List.length_append, List.length_cons, List.length_nil]
    omega

theorem getD_append_cons {α : Type*} (l : List α) (x : α) (d : α) (h : 0 < l.length) :
    List.getD (l ++ [x]) 0 d = List.getD l 0 d :=
  List.getD_append l [x] d 0 h

theorem cget_rFromGamma_zero (γ : List ℚ) (H : ℕ) : cget (rFromGamma γ H) 0 = 1 := by
  induction H with
  | zero => rfl
  | succ H ih =>
    cases h : rFromGamma γ H with
    | nil =>
      have := length_rFromGamma γ H
      rw [h] at this
      simp at this
    | cons y ys =>
      have hform : rFromGamma γ (H + 1) = (y :: ys) ++ [((List.range (H + 1)).map
          fun i => γ.getD (i + 1) 0 * (y :: ys).getD ((H + 1) - 1 - i) 0).sum
            / ((H + 1 : ℕ) : ℚ)] := by
        unfold rFromGamma
        rw [h]
      rw [hform]
      simp
      rw [h] at ih
      exact ih

/-- `R_λ(0) = 1` — the constant term of (18)/(29). -/
theorem Rseries_r0 (hooks : List ℕ) (eEven H : ℕ) : cget (Rseries hooks eEven H) 0 = 1 :=
  cget_rFromGamma_zero _ _

/-! ## Contact polynomials `Q_{r,h}` — equation (20) -/

/-- Generic foldr-sum of `psmul (Rs[h-j]) (A_j)` over an index list. -/
def foldrInner (c2 : ℤ) (cEven : Bool) (Rs : List ℚ) (h : ℕ) (idxs : List ℕ) : List ℚ :=
  idxs.foldr (fun j acc => padd (psmul (Rs.getD (h - j) 0) (Apoly c2 cEven j)) acc) []

theorem cget_foldrInner (c2 : ℤ) (cEven : Bool) (Rs : List ℚ) (h : ℕ) :
    ∀ (idxs : List ℕ) (i : ℕ),
      cget (foldrInner c2 cEven Rs h idxs) i
        = (idxs.map (fun j => Rs.getD (h - j) 0 * cget (Apoly c2 cEven j) i)).sum
  | [], i => rfl
  | j :: js, i => by
    have ih := cget_foldrInner c2 cEven Rs h js i
    show cget (padd (psmul (Rs.getD (h - j) 0) (Apoly c2 cEven j))
        (foldrInner c2 cEven Rs h js)) i
      = _
    rw [cget_padd, cget_psmul, ih]
    simp [List.sum_cons]

/-- `Σ_{j=0}^{h} A_{λ,j}(u) · [w^{h-j}] R_λ`, coefficients in `u`. -/
def innerSum (c2 : ℤ) (cEven : Bool) (Rs : List ℚ) (h : ℕ) : List ℚ :=
  foldrInner c2 cEven Rs h (List.range (h + 1))

theorem cget_innerSum (c2 : ℤ) (cEven : Bool) (Rs : List ℚ) (h i : ℕ) :
    cget (innerSum c2 cEven Rs h) i
      = ((List.range (h + 1)).map fun j =>
          Rs.getD (h - j) 0 * cget (Apoly c2 cEven j) i).sum :=
  cget_foldrInner c2 cEven Rs h _ i

/-- Degree bound of (20): `A_{λ,j}` vanishes above degree `j`. -/
theorem cget_innerSum_of_lt {c2 : ℤ} {cEven : Bool} {Rs : List ℚ} {h i : ℕ}
    (hi : h < i) : cget (innerSum c2 cEven Rs h) i = 0 := by
  rw [cget_innerSum]
  refine List.sum_eq_zero ?_
  intro t ht
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
  have hj' : j ≤ h := by
    have := List.mem_range.mp hj
    omega
  rw [cget_Apoly_of_lt (by omega), mul_zero]

/-- Leading coefficient of the inner sum: only `j = h` contributes to `u^h`. -/
theorem cget_innerSum_self (c2 : ℤ) (cEven : Bool) (Rs : List ℚ) (h : ℕ)
    (hr0 : Rs.getD 0 0 = 1) :
    cget (innerSum c2 cEven Rs h) h
      = ((c2 ^ h : ℤ) : ℚ) / (((2 * h).factorial : ℕ) : ℚ) := by
  rw [cget_innerSum]
  have hsplit : List.range (h + 1) = List.range h ++ [h] := by
    rw [List.range_succ]
  rw [hsplit, List.map_append, List.sum_append]
  have hmid : ((List.range h).map fun j =>
      Rs.getD (h - j) 0 * cget (Apoly c2 cEven j) h).sum = 0 := by
    apply List.sum_eq_zero
    intro t ht
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
    have hj' : j < h := List.mem_range.mp hj
    rw [cget_Apoly_of_lt hj', mul_zero]
  have hlast : (([h]).map fun j =>
      Rs.getD (h - j) 0 * cget (Apoly c2 cEven j) h).sum
      = Rs.getD 0 0 * cget (Apoly c2 cEven h) h := by
    simp
  rw [hmid, hlast, hr0, cget_Apoly_self, one_mul]
  abel_nf

/-- Per-partition contribution to (20). -/
def partQ (r h : ℕ) (ps : List ℕ) : List ℚ :=
  let hooks := partsHooks ps
  let c := partsContent ps
  let c2 := c * c
  let cEven := c % 2 = 0
  let f := partsDim r ps
  let Rs := Rseries hooks (partsEvenHooks ps) h
  psmul (((f * f : ℕ) : ℚ)) (innerSum c2 cEven Rs h)

/-- Sum of a list of polynomials. -/
def sumPoly (l : List (List ℚ)) : List ℚ := l.foldr padd []

theorem cget_sumPoly (l : List (List ℚ)) (i : ℕ) :
    cget (sumPoly l) i = (l.map (fun p => cget p i)).sum := by
  unfold sumPoly
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.foldr_cons, List.map_cons, List.sum_cons, cget_padd, ih]

/-- The contact-order polynomial `Q_{r,h}` of (20), coefficients of `u^0..u^h`. -/
def Qcoeff (r h : ℕ) : List ℚ :=
  psmul (1 / (r.factorial : ℚ))
    (sumPoly ((partitionsOf r).map (partQ r h)))

theorem cget_Qcoeff (r h i : ℕ) :
    cget (Qcoeff r h) i
      = (1 / (r.factorial : ℚ))
          * ((partitionsOf r).map (fun ps => cget (partQ r h ps) i)).sum := by
  unfold Qcoeff
  rw [cget_psmul, cget_sumPoly]
  congr 1
  simp only [List.map_map, Function.comp_apply]
  rfl

/-- Degree bound of Proposition 3.1: `deg Q_{r,h} ≤ h`. -/
theorem Qcoeff_degree (r h : ℕ) (i : ℕ) (hi : h < i) : cget (Qcoeff r h) i = 0 := by
  rw [cget_Qcoeff]
  have hsum : ((partitionsOf r).map (fun ps => cget (partQ r h ps) i)).sum = 0 := by
    refine List.sum_eq_zero ?_
    intro t ht
    obtain ⟨ps, _, rfl⟩ := List.mem_map.mp ht
    unfold partQ
    rw [cget_psmul]
    exact mul_eq_zero_of_right _ (cget_innerSum_of_lt hi)
  rw [hsum, mul_zero]

/-! ## Transposition moments and Proposition 3.2 -/

/-- `Σ_λ (f^λ)² |c_λ|^{2h}` (integer form of (22)). -/
def transpositionMomentInt (r h : ℕ) : ℕ :=
  (partitionsOf r).foldl (fun acc ps =>
    acc + (partsDim r ps) ^ 2 * (partsContent ps).natAbs ^ (2 * h)) 0

/-- `T_h(r)` of (22). -/
def transpositionMoment (r h : ℕ) : ℚ :=
  ((transpositionMomentInt r h : ℕ) : ℚ) / (r.factorial : ℚ)

/-- Sum of squared dimensions `Σ_λ (f^λ)²`. -/
def dimSquareSum (r : ℕ) : ℕ :=
  (partitionsOf r).foldl (fun acc ps => acc + (partsDim r ps) ^ 2) 0


theorem foldl_add_eq_sum (f : List ℕ → ℕ) : ∀ (z : ℕ) (l : List (List ℕ)),
    (l.foldl (fun acc ps => acc + f ps) z) = z + (l.map f).sum
  | z, [] => by simp
  | z, p :: ps => by
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [foldl_add_eq_sum f (z + f p) ps]
    abel_nf

/-- `(c²)^h = |c|^{2h}` as integers. -/
lemma int_sq_pow (c : ℤ) (hn : ℕ) :
    ((c * c) ^ hn : ℤ) = ((c.natAbs ^ (2 * hn) : ℕ) : ℤ) := by
  have e : (c * c : ℤ) = ((c.natAbs : ℕ) : ℤ) ^ 2 := by
    rw [Int.natAbs_sq, pow_two]
  rw [e, ← pow_mul]
  norm_cast
  try rw [Nat.mul_comm]

/-- Proposition 3.2: the coefficient of `u^h` in `Q_{r,h}` is `T_h(r)/(2h)!`. -/
theorem prop_3_2 (r h : ℕ) :
    cget (Qcoeff r h) h = transpositionMoment r h / ((2 * h).factorial) := by
  rw [cget_Qcoeff]
  have hpoint : ∀ (ps : List ℕ),
      cget (partQ r h ps) h
        = (((partsDim r ps) ^ 2 * (partsContent ps).natAbs ^ (2 * h) : ℕ) : ℚ)
            / (((2 * h).factorial : ℕ) : ℚ) := by
    intro ps
    unfold partQ
    rw [cget_psmul, cget_innerSum_self _ _ _ _ (Rseries_r0 _ _ _)]
    rw [int_sq_pow (partsContent ps) h]
    have h2 : ∀ n : ℕ, (((n : ℕ) : ℤ) : ℚ) = ((n : ℕ) : ℚ) := by
      intro n
      norm_cast
    rw [h2]
    have hf : (partsDim r ps * partsDim r ps : ℕ) = (partsDim r ps) ^ 2 :=
      (pow_two _).symm
    rw [hf]
    have h1 : (((partsDim r ps) ^ 2 * (partsContent ps).natAbs ^ (2 * h) : ℕ) : ℚ)
        = (((partsDim r ps) ^ 2 : ℕ) : ℚ)
            * (((partsContent ps).natAbs ^ (2 * h) : ℕ) : ℚ) :=
      Nat.cast_mul _ _
    rw [h1]
    field_simp
    try ring
  have hsum : ((partitionsOf r).map (fun ps => cget (partQ r h ps) h)).sum
      = ((transpositionMomentInt r h : ℕ) : ℚ) / (((2 * h).factorial : ℕ) : ℚ) := by
    have hrew : (partitionsOf r).map (fun ps => cget (partQ r h ps) h)
        = (partitionsOf r).map (fun ps =>
            (((partsDim r ps) ^ 2 * (partsContent ps).natAbs ^ (2 * h) : ℕ) : ℚ)
              / (((2 * h).factorial : ℕ) : ℚ)) :=
      List.map_congr_left (fun ps _ => hpoint ps)
    rw [hrew]
    set D := (((2 * h).factorial : ℕ) : ℚ) with hD
    have hgen : ∀ (ns : List ℕ),
        (ns.map (fun n => (((n : ℕ) : ℚ) / D))).sum
          = (((ns.sum : ℕ) : ℚ) / D) := by
      intro ns
      induction ns with
      | nil => simp
      | cons x xs ih =>
        simp only [List.map_cons, List.sum_cons, ih]
        push_cast
        field_simp
        try ring
    have hfold : ((partitionsOf r).map (fun ps =>
        (partsDim r ps) ^ 2 * (partsContent ps).natAbs ^ (2 * h))).sum
        = transpositionMomentInt r h := by
      unfold transpositionMomentInt
      have h := foldl_add_eq_sum (fun ps =>
        (partsDim r ps) ^ 2 * (partsContent ps).natAbs ^ (2 * h)) 0 (partitionsOf r)
      simpa using h.symm
    have hn := hgen ((partitionsOf r).map (fun ps =>
      (partsDim r ps) ^ 2 * (partsContent ps).natAbs ^ (2 * h)))
    rw [List.map_map] at hn
    rw [hfold] at hn
    exact hn
  rw [hsum]
  unfold transpositionMoment
  field_simp

/-- Necessary leading-coefficient test (23). For `h ≥ 1`:
    `(2h+2)(2h+1) T_h² ≥ (2h)(2h-1) T_{h-1} T_{h+1}`. -/
def leadingCoeffTest (r h : ℕ) : Prop :=
  ((2 * h + 2) * (2 * h + 1) : ℚ) * (transpositionMoment r h) ^ 2
    ≥ ((2 * h) * (2 * h - 1) : ℚ) * transpositionMoment r (h - 1) * transpositionMoment r (h + 1)

/-! ## Proposition 3.1: evaluation form and values at `u = 0` -/

theorem cast_sum_map (f : List ℕ → ℕ) : ∀ (l : List (List ℕ)),
    (((l.map f).sum : ℕ) : ℚ) = (l.map (fun ps => ((f ps : ℕ) : ℚ))).sum
  | [] => by simp
  | p :: ps => by
    simp only [List.map_cons, List.sum_cons, Nat.cast_add]
    rw [cast_sum_map f ps]

theorem Qcoeff_r0_eval (r : ℕ) :
    peval (Qcoeff r 0) 0 = ((dimSquareSum r : ℕ) : ℚ) / (r.factorial : ℚ) := by
  rw [peval_zero, cget_Qcoeff]
  have hpoint : ∀ (ps : List ℕ),
      cget (partQ r 0 ps) 0 = (((partsDim r ps) ^ 2 : ℕ) : ℚ) := by
    intro ps
    unfold partQ
    rw [cget_psmul]
    have hinner : cget (innerSum (partsContent ps * partsContent ps)
        (partsContent ps % 2 = 0)
        (Rseries (partsHooks ps) (partsEvenHooks ps) 0) 0) 0 = 1 := by
      rw [cget_innerSum_self _ _ _ 0 (Rseries_r0 _ _ 0)]
      norm_num
    rw [hinner, mul_one]
    have hf : ((partsDim r ps * partsDim r ps : ℕ) : ℚ) = (((partsDim r ps) ^ 2 : ℕ) : ℚ) :=
      by rw [pow_two]
    exact hf
  have hsum : ((partitionsOf r).map (fun ps => cget (partQ r 0 ps) 0)).sum
      = ((dimSquareSum r : ℕ) : ℚ) := by
    have hrew : (partitionsOf r).map (fun ps => cget (partQ r 0 ps) 0)
        = (partitionsOf r).map (fun ps => (((partsDim r ps) ^ 2 : ℕ) : ℚ)) :=
      List.map_congr_left (fun ps _ => hpoint ps)
    rw [hrew]
    unfold dimSquareSum
    have h := foldl_add_eq_sum (fun ps => (partsDim r ps) ^ 2) 0 (partitionsOf r)
    simp at h
    rw [← cast_sum_map (fun ps => (partsDim r ps) ^ 2) (partitionsOf r), h]
  rw [hsum]
  field_simp
  try ring

/-- Given the standard identity `Σ_λ (f^λ)² = r!` (sum of squares of irreducible
    degrees of `S_r`), `Q_{r,0}(0) = 1`. -/
theorem Qcoeff_r0_one (r : ℕ) (hdim : dimSquareSum r = r.factorial) :
    peval (Qcoeff r 0) 0 = 1 := by
  rw [Qcoeff_r0_eval, hdim]
  exact div_self (by positivity)

/-- Proposition 3.1 at `u = 0` for `h > 0`. External input: `B_{r,0} = τ(Ω) = 1`
    (Prop. 2.3 + dual-basis identity (10)), whose `w^h`-coefficient is `Q_{r,h}(0)`. -/
theorem Qcoeff_h0_zero {r h : ℕ} (_hh : 0 < h)
    (hB : ((partitionsOf r).map (fun ps => cget (partQ r h ps) 0)).sum = 0) :
    peval (Qcoeff r h) 0 = 0 := by
  rw [peval_zero, cget_Qcoeff, hB, mul_zero]

/-- Proposition 3.1 (evaluation form). The remaining obligation is the series
    identity (21) ⇒ (20): the `w`-expansion of `B_{r,k}` equals the partition sum
    (20) at `u = k(k+1)`. Accepting that identity, the BPS coefficient `n_h` equals
    `Q_{r,h}(k(k+1))` and the degree bound holds. -/
theorem prop_3_1 (r k h : ℕ) (n : ℚ)
    (h_eval : n = peval (Qcoeff r h) ((k : ℚ) * (k + 1))) :
    n = peval (Qcoeff r h) ((k : ℚ) * (k + 1))
      ∧ (∀ i, h < i → cget (Qcoeff r h) i = 0) :=
  ⟨h_eval, Qcoeff_degree r h⟩

/-- Full statement of Proposition 3.1 with the isolated external inputs as hypotheses:
    (i) the series identity (21) ⇒ (20);
    (ii) `Σ_λ (f^λ)² = r!`;
    (iii) `Q_{r,h}(0) = 0` for `h > 0` from `B_{r,0} = 1`. -/
theorem prop_3_1_full (r k h : ℕ) (_hr : 2 ≤ r) (_hk : 1 ≤ k) (_hh : h ≤ k * Nat.choose r 2)
    (n : ℚ)
    (hIdent : n = peval (Qcoeff r h) ((k : ℚ) * (k + 1)))
    (hdim : dimSquareSum r = r.factorial)
    (hQ0 : ∀ h', 0 < h' → peval (Qcoeff r h') 0 = 0) :
    n = peval (Qcoeff r h) ((k : ℚ) * (k + 1))
      ∧ (∀ i, h < i → cget (Qcoeff r h) i = 0)
      ∧ (peval (Qcoeff r 0) 0 = 1)
      ∧ (0 < h → peval (Qcoeff r h) 0 = 0) := by
  refine ⟨hIdent, Qcoeff_degree r h, Qcoeff_r0_one r hdim, ?_⟩
  intro hh'
  exact hQ0 h hh'

end Paper20
