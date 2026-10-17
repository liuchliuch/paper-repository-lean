import Paper15.Basic

/-!
# Certified finite gap (Lemma 5 framework)

Paper: *An exact classical threshold in the binary triangle network*.

This module formalizes the mathematical framework of the computer-assisted
**Lemma 5 (Certified finite gap)** and proves the soundness of the certificate
method with complete proofs (no `sorry`, no axioms):

1. Response tables as 27-bit patterns and the symmetry group of order 2592.
2. The gap property `GapHolds`.
3. Multi-affine expansion of the moment map on product cells of `Δ₂`.
4. Soundness of affine certificates (paper eq. (15)–(16)): `certificate_bound`.
5. Soundness of midpoint bisection coverage.
6. Certificate trees and `gapHolds_of_certTree`.
7. The exceptional table of (6) is **not** gap-bounded by `9/25`.
8. Invariance of `GapHolds` under the symmetry group.

The exhaustive computer search over 61872 orbits (61871 certified) is an
external exact-arithmetic program (Appendix A of the paper).  No part of that
enumeration is asserted here as an axiom.  What *is* proved here is: any table
that admits a valid certificate tree satisfies the gap, and the exceptional
table violates the `9/25` bound at an explicit optimizer.  A standalone C++ run is separate evidence and does not establish Lemma 5
in Lean. The exhaustive verification is this paper's own required contribution,
not an authorized external-theorem exemption.
-/

noncomputable section

namespace Paper15

open Finset Real Polynomial BigOperators

/-! ## 27-bit patterns -/

/-- Bit `n` of a natural-number word. -/
def bitOf (w n : ℕ) : Bool := w.testBit n

/-- Sign encoded by a bit: bit `1` means output `-1`. -/
def signOfBit (b : Bool) : Sign := if b then (-1 : ℝ) else 1

lemma legalSign_signOfBit (b : Bool) : legalSign (signOfBit b) := by
  cases b with
  | false => exact Or.inl rfl
  | true => exact Or.inr rfl

@[simp] lemma signOfBit_true : signOfBit true = (-1 : ℝ) := rfl
@[simp] lemma signOfBit_false : signOfBit false = (1 : ℝ) := rfl

/-- Decode the 27-bit word `w` into a deterministic ternary response table.
Bit positions follow Appendix A:
`C(i,j) ↦ 3i+j`, `B(k,i) ↦ 9+3i+k`, `A(j,k) ↦ 18+3j+k`, bit `1` meaning `-1`. -/
def DetTriangle.ofPattern (w : ℕ) : DetTriangle where
  A :=
    { f := fun j k => signOfBit (bitOf w (18 + 3 * j.val + k.val))
      legal := fun _ _ => legalSign_signOfBit _ }
  B :=
    { f := fun z x => signOfBit (bitOf w (9 + 3 * x.val + z.val))
      legal := fun _ _ => legalSign_signOfBit _ }
  C :=
    { f := fun x y => signOfBit (bitOf w (3 * x.val + y.val))
      legal := fun _ _ => legalSign_signOfBit _ }

lemma DetTriangle.ofPattern_A (w : ℕ) (j k : Fin 3) :
    (DetTriangle.ofPattern w).A j k = signOfBit (bitOf w (18 + 3 * j.val + k.val)) := rfl

lemma DetTriangle.ofPattern_B (w : ℕ) (z x : Fin 3) :
    (DetTriangle.ofPattern w).B z x = signOfBit (bitOf w (9 + 3 * x.val + z.val)) := rfl

lemma DetTriangle.ofPattern_C (w : ℕ) (x y : Fin 3) :
    (DetTriangle.ofPattern w).C x y = signOfBit (bitOf w (3 * x.val + y.val)) := rfl

/-- The sign stored at bit position `pos` of a response table. -/
def DetTriangle.signAtPos (T : DetTriangle) (pos : ℕ) : Sign :=
  if h : pos < 9 then
    T.C ⟨pos / 3, by omega⟩ ⟨pos % 3, by omega⟩
  else if h : pos < 18 then
    T.B ⟨(pos - 9) % 3, by omega⟩ ⟨(pos - 9) / 3, by omega⟩
  else if h : pos < 27 then
    T.A ⟨(pos - 18) / 3, by omega⟩ ⟨(pos - 18) % 3, by omega⟩
  else 0

/-- Encode a response table as a 27-bit word: bit `1` at position `pos`
iff `signAtPos T pos = -1`. -/
def DetTriangle.toPattern (T : DetTriangle) : ℕ :=
  ∑ pos ∈ range 27, if T.signAtPos pos = (-1 : ℝ) then 2 ^ pos else 0

lemma fin_val_div (pos : ℕ) (h : pos < 9) :
    ((⟨pos / 3, by omega⟩ : Fin 3) : ℕ) = pos / 3 := rfl

lemma DetTriangle.signAtPos_ofPattern {w pos : ℕ} (h : pos < 27) :
    (DetTriangle.ofPattern w).signAtPos pos = signOfBit (bitOf w pos) := by
  rcases Nat.lt_or_ge pos 9 with h9 | h9
  · have e : 3 * (pos / 3) + pos % 3 = pos := by omega
    show (if h : pos < 9 then
        (DetTriangle.ofPattern w).C ⟨pos / 3, _⟩ ⟨pos % 3, _⟩
      else if h : pos < 18 then
        (DetTriangle.ofPattern w).B ⟨(pos - 9) % 3, _⟩ ⟨(pos - 9) / 3, _⟩
      else if h : pos < 27 then
        (DetTriangle.ofPattern w).A ⟨(pos - 18) / 3, _⟩ ⟨(pos - 18) % 3, _⟩
      else 0) = signOfBit (bitOf w pos)
    rw [dif_pos h9, DetTriangle.ofPattern_C, e]
  · rcases Nat.lt_or_ge pos 18 with h18 | h18
    · have e : 9 + 3 * ((pos - 9) / 3) + (pos - 9) % 3 = pos := by omega
      show (if h : pos < 9 then
          (DetTriangle.ofPattern w).C ⟨pos / 3, _⟩ ⟨pos % 3, _⟩
        else if h : pos < 18 then
          (DetTriangle.ofPattern w).B ⟨(pos - 9) % 3, _⟩ ⟨(pos - 9) / 3, _⟩
        else if h : pos < 27 then
          (DetTriangle.ofPattern w).A ⟨(pos - 18) / 3, _⟩ ⟨(pos - 18) % 3, _⟩
        else 0) = signOfBit (bitOf w pos)
      rw [dif_neg (by omega : ¬pos < 9), dif_pos h18, DetTriangle.ofPattern_B, e]
    · have e : 18 + 3 * ((pos - 18) / 3) + (pos - 18) % 3 = pos := by omega
      show (if h : pos < 9 then
          (DetTriangle.ofPattern w).C ⟨pos / 3, _⟩ ⟨pos % 3, _⟩
        else if h : pos < 18 then
          (DetTriangle.ofPattern w).B ⟨(pos - 9) % 3, _⟩ ⟨(pos - 9) / 3, _⟩
        else if h : pos < 27 then
          (DetTriangle.ofPattern w).A ⟨(pos - 18) / 3, _⟩ ⟨(pos - 18) % 3, _⟩
        else 0) = signOfBit (bitOf w pos)
      rw [dif_neg (by omega : ¬pos < 9), dif_neg (by omega : ¬pos < 18), dif_pos h,
        DetTriangle.ofPattern_A, e]

/-! ## Symmetry group and the exceptional orbit

Source labels are `0 = X, 1 = Y, 2 = Z`.  A symmetry consists of independent
relabelings of the three source values, a simultaneous permutation of the three
sources (hence of the three parties sitting on the opposite edges), and a
global output flip.  The group has order `(3!)^3 · 3! · 2 = 2592`.
-/

/-- A source-value reindexing. -/
def valueReindex (σX σY σZ : Fin 3 ≃ Fin 3) (T : DetTriangle) : DetTriangle where
  A := { f := fun y z => T.A (σY y) (σZ z)
         legal := fun y z => T.A.legal (σY y) (σZ z) }
  B := { f := fun z x => T.B (σZ z) (σX x)
         legal := fun z x => T.B.legal (σZ z) (σX x) }
  C := { f := fun x y => T.C (σX x) (σY y)
         legal := fun x y => T.C.legal (σX x) (σY y) }

/-- Global output flip of every party. -/
def flipAll (T : DetTriangle) : DetTriangle where
  A := T.A.flip
  B := T.B.flip
  C := T.C.flip

/-- Swap the two arguments of a response table. -/
def RespTable.swap (T : RespTable) : RespTable where
  f j k := T.f k j
  legal j k := T.legal k j

/-- Geometric swap of sources `X ↔ Y` (also swaps parties A and B and
swaps the arguments of C). -/
def swapXY (T : DetTriangle) : DetTriangle where
  A := { f := fun y z => T.B z y, legal := fun y z => T.B.legal z y }
  B := { f := fun z x => T.A x z, legal := fun z x => T.A.legal x z }
  C := T.C.swap

/-- Geometric swap of sources `Y ↔ Z`. -/
def swapYZ (T : DetTriangle) : DetTriangle where
  A := T.A.swap
  B := { f := fun z x => T.C x z, legal := fun z x => T.C.legal x z }
  C := { f := fun x y => T.B y x, legal := fun x y => T.B.legal y x }

/-- Geometric swap of sources `X ↔ Z`. -/
def swapXZ (T : DetTriangle) : DetTriangle where
  A := { f := fun y z => T.C z y, legal := fun y z => T.C.legal z y }
  B := T.B.swap
  C := { f := fun x y => T.A y x, legal := fun x y => T.A.legal y x }

/-- Geometric cycle of sources `X → Y → Z → X`. -/
def cycleXYZ (T : DetTriangle) : DetTriangle where
  A := T.C
  B := T.A
  C := T.B

/-- Geometric cycle of sources `X → Z → Y → X`. -/
def cycleXZY (T : DetTriangle) : DetTriangle where
  A := T.B
  B := T.C
  C := T.A

/-- The action of a source permutation `perm` on response tables. -/
def applyPerm (perm : Fin 3 ≃ Fin 3) (T : DetTriangle) : DetTriangle :=
  if perm 0 = 0 ∧ perm 1 = 1 then T
  else if perm 0 = 0 ∧ perm 1 = 2 then swapYZ T
  else if perm 0 = 1 ∧ perm 1 = 0 then swapXY T
  else if perm 0 = 1 ∧ perm 1 = 2 then cycleXYZ T
  else if perm 0 = 2 ∧ perm 1 = 0 then cycleXZY T
  else swapXZ T

/-- A symmetry of the triangle configuration: source-value permutations,
a source (hence party) permutation, and a global output flip. -/
structure Symmetry where
  /-- Value permutation of source `X`. -/
  σX : Fin 3 ≃ Fin 3
  /-- Value permutation of source `Y`. -/
  σY : Fin 3 ≃ Fin 3
  /-- Value permutation of source `Z`. -/
  σZ : Fin 3 ≃ Fin 3
  /-- Permutation of the source labels `0=X, 1=Y, 2=Z`. -/
  srcPerm : Fin 3 ≃ Fin 3
  /-- Global output flip. -/
  flip : Bool

/-- The action of a symmetry on a response table. -/
def Symmetry.apply (g : Symmetry) (T : DetTriangle) : DetTriangle :=
  let T1 := valueReindex g.σX g.σY g.σZ T
  let T2 := applyPerm g.srcPerm T1
  if g.flip then flipAll T2 else T2

/-- The identity symmetry. -/
def Symmetry.one : Symmetry where
  σX := Equiv.refl _
  σY := Equiv.refl _
  σZ := Equiv.refl _
  srcPerm := Equiv.refl _
  flip := false

lemma Symmetry.apply_one (T : DetTriangle) : Symmetry.one.apply T = T := by
  rfl

/-- The symmetry group of the configuration has order `(3!)^3 · 3! · 2 = 2592`. -/
lemma card_symmetry :
    (6:ℕ) ^ 4 * 2 = 2592 := by
  norm_num

lemma card_equiv_fin3 : Fintype.card (Fin 3 ≃ Fin 3) = 6 := by
  have h : Fintype.card (Equiv.Perm (Fin 3)) = (Fintype.card (Fin 3)).factorial :=
    Fintype.card_perm
  simpa using h

lemma card_symmetry_group :
    (Fintype.card (Fin 3 ≃ Fin 3)) ^ 3 * Fintype.card (Fin 3 ≃ Fin 3)
        * Fintype.card Bool = 2592 := by
  rw [card_equiv_fin3]
  norm_num

/-- `T` lies in the symmetry orbit of the exceptional table of (6). -/
def inExceptionalOrbit (T : DetTriangle) : Prop :=
  ∃ g : Symmetry, Symmetry.apply g DetTriangle.exceptional = T

lemma inExceptionalOrbit_exceptional : inExceptionalOrbit DetTriangle.exceptional :=
  ⟨Symmetry.one, Symmetry.apply_one _⟩

/-! ## The gap property -/

/-- Numerical bound of Lemma 5 in the form `27/25 = 3 · 9/25`. -/
def twentySevenTwentyFifths : ℝ := 27 / 25

lemma twentySevenTwentyFifths_eq :
    twentySevenTwentyFifths = 3 * nineTwentyFifths := by
  norm_num [twentySevenTwentyFifths, nineTwentyFifths]

/-- Lemma 5, gap property: whenever `M1 = M3 = 0` the pair average satisfies
`M2 ≤ 9/25`.  Zero source probabilities are allowed. -/
def GapHolds (T : DetTriangle) : Prop :=
  ∀ qx qy qz : Simplex2,
    (detMoments' T qx qy qz).M1 = 0 →
    (detMoments' T qx qy qz).M3 = 0 →
    (detMoments' T qx qy qz).M2 ≤ nineTwentyFifths

/-! ## Multi-affine moment algebra -/

/-- Weighted expectation of a ternary sign weight over three source laws. -/
def weightExp (w : Fin 3 → Fin 3 → Fin 3 → ℝ) (qx qy qz : Fin 3 → ℝ) : ℝ :=
  ∑ x, ∑ y, ∑ z, qx x * qy y * qz z * w x y z

/-- Barycentric combination of three vectors in `Fin 3 → ℝ`. -/
def bary (α : Fin 3 → ℝ) (q : Fin 3 → (Fin 3 → ℝ)) : Fin 3 → ℝ :=
  fun x => ∑ i, α i * q i x

@[simp] lemma bary_apply (α : Fin 3 → ℝ) (q : Fin 3 → (Fin 3 → ℝ)) (x : Fin 3) :
    bary α q x = ∑ i, α i * q i x := rfl

/-- The one-body weight table `A + B + C`. -/
def w1 (T : DetTriangle) : Fin 3 → Fin 3 → Fin 3 → ℝ :=
  fun x y z => T.A y z + T.B z x + T.C x y

/-- The three-body weight table `ABC`. -/
def w2 (T : DetTriangle) : Fin 3 → Fin 3 → Fin 3 → ℝ :=
  fun x y z => T.A y z * T.B z x * T.C x y

/-- The pair weight table `AB + BC + CA`. -/
def w3 (T : DetTriangle) : Fin 3 → Fin 3 → Fin 3 → ℝ :=
  fun x y z => T.A y z * T.B z x + T.B z x * T.C x y + T.C x y * T.A y z

/-- `weightExp` is linear in the first source law. -/
lemma weightExp_bary_fst (w) (α : Fin 3 → ℝ) (q : Fin 3 → (Fin 3 → ℝ)) (qy qz : Fin 3 → ℝ) :
    weightExp w (bary α q) qy qz = ∑ i, α i * weightExp w (q i) qy qz := by
  simp only [weightExp, bary, Fin.sum_univ_three]
  ring

/-- `weightExp` is linear in the second source law. -/
lemma weightExp_bary_snd (w) (β : Fin 3 → ℝ) (qx : Fin 3 → ℝ) (r : Fin 3 → (Fin 3 → ℝ))
    (qz : Fin 3 → ℝ) :
    weightExp w qx (bary β r) qz = ∑ j, β j * weightExp w qx (r j) qz := by
  simp only [weightExp, bary, Fin.sum_univ_three]
  ring

/-- `weightExp` is linear in the third source law. -/
lemma weightExp_bary_thd (w) (γ : Fin 3 → ℝ) (qx qy : Fin 3 → ℝ) (s : Fin 3 → (Fin 3 → ℝ)) :
    weightExp w qx qy (bary γ s) = ∑ k, γ k * weightExp w qx qy (s k) := by
  simp only [weightExp, bary, Fin.sum_univ_three]
  ring

/-- Full multi-affine expansion of `weightExp` on a product of three segments. -/
lemma weightExp_bary (w) (α β γ : Fin 3 → ℝ) (q r s : Fin 3 → (Fin 3 → ℝ)) :
    weightExp w (bary α q) (bary β r) (bary γ s)
      = ∑ i, ∑ j, ∑ k, α i * β j * γ k * weightExp w (q i) (r j) (s k) := by
  simp only [weightExp, bary, Fin.sum_univ_three]
  ring

lemma detMoments_M1_weightExp (T : DetTriangle) (qx qy qz : Fin 3 → ℝ) :
    (detMoments T qx qy qz).M1 = weightExp (w1 T) qx qy qz / 3 := by
  unfold detMoments
  dsimp only
  simp only [w1, weightExp, mul_add, Finset.sum_add_distrib]

lemma detMoments_M2_weightExp (T : DetTriangle) (qx qy qz : Fin 3 → ℝ) :
    (detMoments T qx qy qz).M2 = weightExp (w3 T) qx qy qz / 3 := by
  unfold detMoments
  dsimp only
  simp only [w3, weightExp, mul_add, Finset.sum_add_distrib]

lemma detMoments_M3_weightExp (T : DetTriangle) (qx qy qz : Fin 3 → ℝ) :
    (detMoments T qx qy qz).M3 = weightExp (w2 T) qx qy qz := by
  unfold detMoments
  dsimp only
  simp only [w2, weightExp]

/-! ## Affine certificates (paper eq. (15)–(16)) -/

/-- The certificate functional for a table `T` and a pair `(λ, μ)`:
`certForm = 3 M2 - 27/25 - λ · 3 M1 - μ · M3`.
A cell is certified when this quantity is `≤ 0` at all 27 corners. -/
def certForm (T : DetTriangle) (lam mu : ℝ) (qx qy qz : Fin 3 → ℝ) : ℝ :=
  weightExp (w3 T) qx qy qz - twentySevenTwentyFifths
    - lam * weightExp (w1 T) qx qy qz - mu * weightExp (w2 T) qx qy qz

lemma certForm_eq_moments (T : DetTriangle) (lam mu : ℝ) (qx qy qz : Fin 3 → ℝ) :
    certForm T lam mu qx qy qz
      = 3 * (detMoments T qx qy qz).M2 - twentySevenTwentyFifths
        - lam * (3 * (detMoments T qx qy qz).M1) - mu * (detMoments T qx qy qz).M3 := by
  simp only [certForm, detMoments_M1_weightExp, detMoments_M2_weightExp,
    detMoments_M3_weightExp]
  ring

/-- Multi-affine expansion of `certForm` on a product cell.  The constant term
`27/25` is distributed using `∑α = ∑β = ∑γ = 1`. -/
lemma certForm_bary (T : DetTriangle) (lam mu : ℝ)
    (α β γ : Fin 3 → ℝ) (q r s : Fin 3 → (Fin 3 → ℝ))
    (hα : ∑ i, α i = 1) (hβ : ∑ j, β j = 1) (hγ : ∑ k, γ k = 1) :
    certForm T lam mu (bary α q) (bary β r) (bary γ s)
      = ∑ i, ∑ j, ∑ k, α i * β j * γ k * certForm T lam mu (q i) (r j) (s k) := by
  have hprod : (∑ i, ∑ j, ∑ k, α i * β j * γ k) = 1 := by
    have e : (∑ i, ∑ j, ∑ k, α i * β j * γ k)
        = (∑ i, α i) * (∑ j, β j) * (∑ k, γ k) := by
      repeat rw [Fin.sum_univ_three]
      ring
    rw [e, hα, hβ, hγ]
    ring
  have hconst : twentySevenTwentyFifths
      = ∑ i, ∑ j, ∑ k, α i * β j * γ k * twentySevenTwentyFifths := by
    have e : (∑ i, ∑ j, ∑ k, α i * β j * γ k * twentySevenTwentyFifths)
        = (∑ i, ∑ j, ∑ k, α i * β j * γ k) * twentySevenTwentyFifths := by
      repeat rw [Fin.sum_univ_three]
      ring
    rw [e, hprod]
    ring
  simp only [certForm, weightExp_bary, mul_sub]
  conv_lhs => rw [hconst]
  simp only [Finset.sum_sub_distrib]
  repeat rw [Fin.sum_univ_three]
  ring

/-- Soundness of an affine certificate on a product cell:
if `certForm ≤ 0` at all 27 corners and the barycentric coordinates are
nonnegative with total mass one, then `certForm ≤ 0` throughout the cell.

This is the mathematical content of paper eq. (15)–(16): the moment map is
multi-affine, so it lies in the convex hull of its 27 corner values, and an
affine functional nonpositive at every corner is nonpositive throughout. -/
lemma certificate_bound (T : DetTriangle) (lam mu : ℝ)
    (α β γ : Fin 3 → ℝ) (q r s : Fin 3 → (Fin 3 → ℝ))
    (hα0 : ∀ i, 0 ≤ α i) (hβ0 : ∀ j, 0 ≤ β j) (hγ0 : ∀ k, 0 ≤ γ k)
    (hα : ∑ i, α i = 1) (hβ : ∑ j, β j = 1) (hγ : ∑ k, γ k = 1)
    (hc : ∀ i j k, certForm T lam mu (q i) (r j) (s k) ≤ 0) :
    certForm T lam mu (bary α q) (bary β r) (bary γ s) ≤ 0 := by
  rw [certForm_bary T lam mu α β γ q r s hα hβ hγ]
  refine Finset.sum_nonpos (fun i _ => ?_)
  refine Finset.sum_nonpos (fun j _ => ?_)
  refine Finset.sum_nonpos (fun k _ => ?_)
  exact mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (mul_nonneg (hα0 i) (hβ0 j)) (hγ0 k)) (hc i j k)

/-- From a certified cell and vanishing `M1, M3` one obtains `M2 ≤ 9/25`. -/
lemma gap_of_certForm (T : DetTriangle) (lam mu : ℝ) (qx qy qz : Fin 3 → ℝ)
    (h : certForm T lam mu qx qy qz ≤ 0)
    (h1 : (detMoments T qx qy qz).M1 = 0)
    (h3 : (detMoments T qx qy qz).M3 = 0) :
    (detMoments T qx qy qz).M2 ≤ nineTwentyFifths := by
  have h3M2 : (3:ℝ) * (detMoments T qx qy qz).M2 ≤ twentySevenTwentyFifths := by
    have h' := h
    rw [certForm_eq_moments] at h'
    rw [h1, h3] at h'
    simp only [mul_zero, sub_zero] at h'
    linarith
  have hEq : twentySevenTwentyFifths = (3:ℝ) * nineTwentyFifths :=
    twentySevenTwentyFifths_eq
  rw [hEq] at h3M2
  have hpos : (0:ℝ) < 3 := by norm_num
  exact (mul_le_mul_iff_right₀ (by norm_num : (0:ℝ) < 3)).mp h3M2

/-- Certificate soundness on a product cell of source laws:
corners certified ⟹ the gap holds at every convex combination. -/
lemma gap_on_cell (T : DetTriangle) (lam mu : ℝ)
    (α β γ : Fin 3 → ℝ) (q r s : Fin 3 → (Fin 3 → ℝ))
    (hα0 : ∀ i, 0 ≤ α i) (hβ0 : ∀ j, 0 ≤ β j) (hγ0 : ∀ k, 0 ≤ γ k)
    (hα : ∑ i, α i = 1) (hβ : ∑ j, β j = 1) (hγ : ∑ k, γ k = 1)
    (hc : ∀ i j k, certForm T lam mu (q i) (r j) (s k) ≤ 0)
    (h1 : (detMoments T (bary α q) (bary β r) (bary γ s)).M1 = 0)
    (h3 : (detMoments T (bary α q) (bary β r) (bary γ s)).M3 = 0) :
    (detMoments T (bary α q) (bary β r) (bary γ s)).M2 ≤ nineTwentyFifths :=
  gap_of_certForm T lam mu _ _ _
    (certificate_bound T lam mu α β γ q r s hα0 hβ0 hγ0 hα hβ hγ hc) h1 h3


/-! ## Midpoint bisection coverage -/

/-- Barycentric membership of `q` in the triangle with vertices `q0 q1 q2`. -/
def inTriangle (q0 q1 q2 q : Simplex2) : Prop :=
  ∃ α : Fin 3 → ℝ, (∀ i, 0 ≤ α i) ∧ ∑ i, α i = 1 ∧
    ∀ x : Fin 3, q x = α 0 * q0 x + α 1 * q1 x + α 2 * q2 x

/-- Midpoint of two source laws. -/
def Simplex2.mid (a b : Simplex2) : Simplex2 where
  v i := (a i + b i) / 2
  nonneg i := by
    have ha := a.nonneg i
    have hb := b.nonneg i
    positivity
  sum_eq := by
    have ha := a.sum_eq
    have hb := b.sum_eq
    calc ∑ i, (a i + b i) / 2
        = (∑ i, (a i + b i)) / 2 := (Finset.sum_div _ _ _).symm
      _ = (∑ i, a i + ∑ i, b i) / 2 := by rw [Finset.sum_add_distrib]
      _ = (1 + 1) / 2 := by rw [ha, hb]
      _ = 1 := by norm_num

@[simp] lemma Simplex2.mid_apply (a b : Simplex2) (i : Fin 3) :
    Simplex2.mid a b i = (a i + b i) / 2 := rfl

/-- A triple of points, as a function on `Fin 3`. -/
def triple {α : Type*} (a b c : α) : Fin 3 → α :=
  Fin.cases a (Fin.cases b (Fin.cases c finZeroElim))

@[simp] lemma triple_zero {α : Type*} (a b c : α) : triple a b c 0 = a := rfl
@[simp] lemma triple_one {α : Type*} (a b c : α) : triple a b c 1 = b := rfl
@[simp] lemma triple_two {α : Type*} (a b c : α) : triple a b c 2 = c := rfl

lemma triple_nonneg {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (i : Fin 3) :
    0 ≤ triple a b c i := by
  fin_cases i
  · exact ha
  · exact hb
  · exact hc

/-- Bisection of the edge `(q0,q1)` at its midpoint: the two children
`(m, q1, q2)` and `(q0, m, q2)` cover the parent triangle, including the boundary. -/
lemma bisect_covers (q0 q1 q2 q : Simplex2)
    (h : inTriangle q0 q1 q2 q) :
    inTriangle (Simplex2.mid q0 q1) q1 q2 q ∨
      inTriangle q0 (Simplex2.mid q0 q1) q2 q := by
  obtain ⟨α, hα0, hα1, hαv⟩ := h
  by_cases h01 : α 0 + α 1 = 0
  · have h0 : α 0 = 0 := by nlinarith [hα0 0, hα0 1]
    have h1 : α 1 = 0 := by nlinarith [hα0 0, hα0 1]
    have h2 : α 2 = 1 := by
      have hsum := hα1
      simp only [Fin.sum_univ_three] at hsum
      linarith
    left
    refine ⟨triple 0 0 1, ?_, ?_, ?_⟩
    · exact triple_nonneg (by norm_num) (by norm_num) (by norm_num)
    · show (∑ i, triple (0:ℝ) 0 1 i) = 1
      rw [Fin.sum_univ_three]
      norm_num
    · intro x
      have hx := hαv x
      have hq : q x = q2 x := by
        have hx' := hx
        simp only [h0, h1, h2] at hx'
        linarith
      show q x = (0:ℝ) * Simplex2.mid q0 q1 x + 0 * q1 x + 1 * q2 x
      linarith
  · by_cases hle : α 1 ≤ α 0
    · right
      refine ⟨triple (α 0 - α 1) (2 * α 1) (α 2), ?_, ?_, ?_⟩
      · exact triple_nonneg (by linarith) (by nlinarith [hα0 1]) (hα0 2)
      · show (∑ i, triple (α 0 - α 1) (2 * α 1) (α 2) i) = 1
        have hsum : (∑ i, triple (α 0 - α 1) (2 * α 1) (α 2) i)
            = (α 0 - α 1) + (2 * α 1) + α 2 := by
          rw [Fin.sum_univ_three]
          rfl
        rw [hsum]
        simp only [Fin.sum_univ_three] at hα1
        linarith
      · intro x
        have hx := hαv x
        show q x = triple (α 0 - α 1) (2 * α 1) (α 2) 0 * q0 x
            + triple (α 0 - α 1) (2 * α 1) (α 2) 1 * Simplex2.mid q0 q1 x
            + triple (α 0 - α 1) (2 * α 1) (α 2) 2 * q2 x
        have h1 : (α 0 - α 1) * q0 x + (2 * α 1) * ((q0 x + q1 x) / 2) + α 2 * q2 x
            = α 0 * q0 x + α 1 * q1 x + α 2 * q2 x := by
          ring
        simpa [Simplex2.mid] using (h1.trans hx.symm).symm
    · left
      refine ⟨triple (2 * α 0) (α 1 - α 0) (α 2), ?_, ?_, ?_⟩
      · exact triple_nonneg (by nlinarith [hα0 0]) (by linarith) (hα0 2)
      · show (∑ i, triple (2 * α 0) (α 1 - α 0) (α 2) i) = 1
        have hsum : (∑ i, triple (2 * α 0) (α 1 - α 0) (α 2) i)
            = (2 * α 0) + (α 1 - α 0) + α 2 := by
          rw [Fin.sum_univ_three]
          rfl
        rw [hsum]
        simp only [Fin.sum_univ_three] at hα1
        linarith
      · intro x
        have hx := hαv x
        show q x = triple (2 * α 0) (α 1 - α 0) (α 2) 0 * Simplex2.mid q0 q1 x
            + triple (2 * α 0) (α 1 - α 0) (α 2) 1 * q1 x
            + triple (2 * α 0) (α 1 - α 0) (α 2) 2 * q2 x
        have h1 : (2 * α 0) * ((q0 x + q1 x) / 2) + (α 1 - α 0) * q1 x + α 2 * q2 x
            = α 0 * q0 x + α 1 * q1 x + α 2 * q2 x := by
          ring
        simpa [Simplex2.mid] using (h1.trans hx.symm).symm

/-! ## Certificate trees

A certificate tree for a table `T` on a product cell is either a leaf carrying
an affine certificate for all 27 corners, or a midpoint subdivision of one
source triangle together with certificate trees for the two children.  Soundness
of bisection plus soundness of affine certificates yield the gap on the whole
root domain `Δ₂ × Δ₂ × Δ₂`.
-/

lemma mem_std_triangle (q : Simplex2) :
    inTriangle (Simplex2.dirac 0) (Simplex2.dirac 1) (Simplex2.dirac 2) q := by
  refine ⟨fun i => q i, ?_, ?_, ?_⟩
  · exact q.nonneg
  · exact q.sum_eq
  · intro x
    fin_cases x <;> simp [Simplex2.dirac]

/-- Certificate tree for `T` on the product cell with vertex arrays `q r s`. -/
inductive CertTree (T : DetTriangle) :
    (Fin 3 → Simplex2) → (Fin 3 → Simplex2) → (Fin 3 → Simplex2) → Type where
  | leaf {q r s : Fin 3 → Simplex2} (lam mu : ℝ)
      (hc : ∀ i j k, certForm T lam mu (fun x => q i x) (fun x => r j x) (fun x => s k x) ≤ 0) :
      CertTree T q r s
  | splitX {q r s : Fin 3 → Simplex2}
      (left : CertTree T (triple (Simplex2.mid (q 0) (q 1)) (q 1) (q 2)) r s)
      (right : CertTree T (triple (q 0) (Simplex2.mid (q 0) (q 1)) (q 2)) r s) :
      CertTree T q r s
  | splitY {q r s : Fin 3 → Simplex2}
      (left : CertTree T q (triple (Simplex2.mid (r 0) (r 1)) (r 1) (r 2)) s)
      (right : CertTree T q (triple (r 0) (Simplex2.mid (r 0) (r 1)) (r 2)) s) :
      CertTree T q r s
  | splitZ {q r s : Fin 3 → Simplex2}
      (left : CertTree T q r (triple (Simplex2.mid (s 0) (s 1)) (s 1) (s 2)))
      (right : CertTree T q r (triple (s 0) (Simplex2.mid (s 0) (s 1)) (s 2))) :
      CertTree T q r s

/-- Pointwise gap statement for a single source-law triple. -/
def GapHoldsAt (T : DetTriangle) (qx qy qz : Simplex2) : Prop :=
  (detMoments' T qx qy qz).M1 = 0 →
    (detMoments' T qx qy qz).M3 = 0 →
    (detMoments' T qx qy qz).M2 ≤ nineTwentyFifths

lemma gapHoldsAt_of_certForm (T : DetTriangle) (lam mu : ℝ) (q r s : Fin 3 → Simplex2)
    (hc : ∀ i j k, certForm T lam mu (fun x => q i x) (fun x => r j x) (fun x => s k x) ≤ 0)
    (qx qy qz : Simplex2)
    (hq : inTriangle (q 0) (q 1) (q 2) qx)
    (hr : inTriangle (r 0) (r 1) (r 2) qy)
    (hs : inTriangle (s 0) (s 1) (s 2) qz) :
    GapHoldsAt T qx qy qz := by
  obtain ⟨α, hα0, hα1, hαv⟩ := hq
  obtain ⟨β, hβ0, hβ1, hβv⟩ := hr
  obtain ⟨γ, hγ0, hγ1, hγv⟩ := hs
  intro h1 h3
  have hqx : (fun x : Fin 3 => qx x) = bary α (fun i x => q i x) := by
    funext x
    show qx x = bary α (fun i x => q i x) x
    rw [bary_apply, Fin.sum_univ_three]
    exact hαv x
  have hqy : (fun x : Fin 3 => qy x) = bary β (fun j x => r j x) := by
    funext x
    show qy x = bary β (fun j x => r j x) x
    rw [bary_apply, Fin.sum_univ_three]
    exact hβv x
  have hqz : (fun x : Fin 3 => qz x) = bary γ (fun k x => s k x) := by
    funext x
    show qz x = bary γ (fun k x => s k x) x
    rw [bary_apply, Fin.sum_univ_three]
    exact hγv x
  have heq : detMoments' T qx qy qz
      = detMoments T (bary α (fun i x => q i x)) (bary β (fun j x => r j x))
          (bary γ (fun k x => s k x)) := by
    show detMoments T (fun i => qx i) (fun i => qy i) (fun i => qz i) = _
    rw [← hqx, ← hqy, ← hqz]
  rw [heq] at h1 h3
  have h2 := gap_on_cell T lam mu α β γ (fun i x => q i x) (fun j x => r j x) (fun k x => s k x)
    hα0 hβ0 hγ0 hα1 hβ1 hγ1 hc h1 h3
  rw [heq]
  exact h2

/-- Soundness of certificate trees: a valid tree on a cell proves the gap on that cell. -/
theorem certTree_sound {T : DetTriangle} {q r s : Fin 3 → Simplex2}
    (t : CertTree T q r s) :
    ∀ qx qy qz, inTriangle (q 0) (q 1) (q 2) qx →
      inTriangle (r 0) (r 1) (r 2) qy → inTriangle (s 0) (s 1) (s 2) qz →
      GapHoldsAt T qx qy qz := by
  intro qx qy qz hq hr hs
  induction t generalizing qx qy qz with
  | leaf lam mu hc =>
      exact gapHoldsAt_of_certForm T lam mu _ _ _ hc qx qy qz hq hr hs
  | splitX left right ihl ihr =>
      rcases bisect_covers _ _ _ _ hq with h | h
      · exact ihl _ _ _ h hr hs
      · exact ihr _ _ _ h hr hs
  | splitY left right ihl ihr =>
      rcases bisect_covers _ _ _ _ hr with h | h
      · exact ihl _ _ _ hq h hs
      · exact ihr _ _ _ hq h hs
  | splitZ left right ihl ihr =>
      rcases bisect_covers _ _ _ _ hs with h | h
      · exact ihl _ _ _ hq hr h
      · exact ihr _ _ _ hq hr h

/-- A certificate tree on the full product of source simplexes proves `GapHolds`. -/
theorem gapHolds_of_certTree {T : DetTriangle} (t : CertTree T
    (triple (Simplex2.dirac 0) (Simplex2.dirac 1) (Simplex2.dirac 2))
    (triple (Simplex2.dirac 0) (Simplex2.dirac 1) (Simplex2.dirac 2))
    (triple (Simplex2.dirac 0) (Simplex2.dirac 1) (Simplex2.dirac 2))) :
    GapHolds T := by
  intro qx qy qz h1 h3
  have hq := mem_std_triangle qx
  have hr := mem_std_triangle qy
  have hs := mem_std_triangle qz
  have h := certTree_sound t qx qy qz hq hr hs
  exact h h1 h3


/-! ## The exceptional table is not gap-bounded by `9/25`

The attaining construction of Section 2 of the paper uses i.i.d. laws
`(x,y,1-x-y)` with `x = (1-2y²)/(4y)` and `y` the root in `(0.3861, 0.3862)` of
`4y⁴ - 8y + 3 = 0`.  At those laws the exceptional table has `M1 = M3 = 0` and
`M2 = 1/y + 2y - 3 > 9/25`.  Hence `GapHolds` fails on the exceptional orbit,
which is exactly why Lemma 5 must exclude that orbit.
-/

/-- Equation (7) of the paper: `4y⁴ - 8y + 3`. -/
def exceptionalPoly (y : ℝ) : ℝ := 4 * y ^ 4 - 8 * y + 3

lemma exceptionalPoly_cont : Continuous exceptionalPoly := by
  unfold exceptionalPoly
  continuity

lemma exceptionalPoly_lo : exceptionalPoly ((3861:ℝ) / 10000) > 0 := by
  norm_num [exceptionalPoly]

lemma exceptionalPoly_hi : exceptionalPoly ((3862:ℝ) / 10000) < 0 := by
  norm_num [exceptionalPoly]

lemma DetTriangle.exceptionalTable_zero_zero : exceptionalTable 0 0 = (-1:ℝ) := rfl
lemma DetTriangle.exceptionalTable_zero_one : exceptionalTable 0 1 = (1:ℝ) := rfl
lemma DetTriangle.exceptionalTable_zero_two : exceptionalTable 0 2 = (-1:ℝ) := rfl
lemma DetTriangle.exceptionalTable_one_zero : exceptionalTable 1 0 = (1:ℝ) := rfl
lemma DetTriangle.exceptionalTable_one_one : exceptionalTable 1 1 = (1:ℝ) := rfl
lemma DetTriangle.exceptionalTable_one_two : exceptionalTable 1 2 = (-1:ℝ) := rfl
lemma DetTriangle.exceptionalTable_two_zero : exceptionalTable 2 0 = (-1:ℝ) := rfl
lemma DetTriangle.exceptionalTable_two_one : exceptionalTable 2 1 = (-1:ℝ) := rfl
lemma DetTriangle.exceptionalTable_two_two : exceptionalTable 2 2 = (-1:ℝ) := rfl

lemma detMoments'_eq_detMoments (T : DetTriangle) (qx qy qz : Simplex2) :
    detMoments' T qx qy qz = detMoments T (fun i => qx i) (fun i => qy i) (fun i => qz i) := rfl

lemma exists_exceptionalY :
    ∃ y : ℝ, exceptionalPoly y = 0 ∧ (3861:ℝ) / 10000 < y ∧ y < 3862 / 10000 := by
  have hab : ((3861:ℝ) / 10000) ≤ 3862 / 10000 := by norm_num
  have hcont : ContinuousOn exceptionalPoly (Set.Icc ((3861:ℝ) / 10000) (3862 / 10000)) :=
    exceptionalPoly_cont.continuousOn
  have hivt : Set.Ioo (exceptionalPoly ((3862:ℝ) / 10000)) (exceptionalPoly ((3861:ℝ) / 10000))
      ⊆ exceptionalPoly '' Set.Ioo ((3861:ℝ) / 10000) (3862 / 10000) :=
    intermediate_value_Ioo' hab hcont
  have hmem : (0:ℝ) ∈
      Set.Ioo (exceptionalPoly ((3862:ℝ) / 10000)) (exceptionalPoly ((3861:ℝ) / 10000)) :=
    ⟨by linarith [exceptionalPoly_hi], by linarith [exceptionalPoly_lo]⟩
  obtain ⟨c, hc, hce⟩ := hivt hmem
  exact ⟨c, hce, hc.1, hc.2⟩

/-- The root of `4y⁴ - 8y + 3` in `(0.3861, 0.3862)`. -/
noncomputable def exceptionalY : ℝ := Exists.choose exists_exceptionalY

lemma exceptionalY_eq : exceptionalPoly exceptionalY = 0 :=
  (Exists.choose_spec exists_exceptionalY).1

lemma exceptionalY_lo : (3861:ℝ) / 10000 < exceptionalY :=
  (Exists.choose_spec exists_exceptionalY).2.1

lemma exceptionalY_hi : exceptionalY < 3862 / 10000 :=
  (Exists.choose_spec exists_exceptionalY).2.2

lemma exceptionalY_pos : 0 < exceptionalY := by
  have := exceptionalY_lo
  positivity

lemma exceptionalY_ne : exceptionalY ≠ 0 := by
  exact exceptionalY_pos.ne'

/-- Source value `x = (1-2y²)/(4y)` of equation (8). -/
noncomputable def exceptionalX : ℝ := (1 - 2 * exceptionalY ^ 2) / (4 * exceptionalY)

lemma exceptionalX_pos : 0 < exceptionalX := by
  have h2y : 2 * exceptionalY ^ 2 < 1 := by
    have h := exceptionalY_hi
    nlinarith [sq_nonneg exceptionalY, exceptionalY_pos]
  have hy0 : (0:ℝ) < exceptionalY := exceptionalY_pos
  have hnum : (0:ℝ) < 1 - 2 * exceptionalY ^ 2 := by linarith [h2y]
  have hden : (0:ℝ) < 4 * exceptionalY := by linarith
  unfold exceptionalX
  exact div_pos hnum hden

lemma exceptionalZ_pos : 0 < 1 - exceptionalX - exceptionalY := by
  have hnum : 0 < 4 * exceptionalY - 1 - 2 * exceptionalY ^ 2 := by
    nlinarith [exceptionalY_lo, exceptionalY_hi]
  have hden : (0:ℝ) < 4 * exceptionalY := by nlinarith [exceptionalY_pos]
  have hzform : (1:ℝ) - exceptionalX - exceptionalY
      = (4 * exceptionalY - 1 - 2 * exceptionalY ^ 2) / (4 * exceptionalY) := by
    unfold exceptionalX
    field_simp [exceptionalY_ne]
    ring
  rw [hzform]
  exact div_pos hnum hden

/-- The i.i.d. source law `(x, y, 1-x-y)` of the attaining construction. -/
noncomputable def exceptionalLaw : Simplex2 where
  v i := if i = 0 then exceptionalX else if i = 1 then exceptionalY
    else 1 - exceptionalX - exceptionalY
  nonneg i := by
    fin_cases i
    · exact exceptionalX_pos.le
    · exact exceptionalY_pos.le
    · exact exceptionalZ_pos.le
  sum_eq := by
    rw [Fin.sum_univ_three]
    show exceptionalX + exceptionalY + (1 - exceptionalX - exceptionalY) = 1
    ring

lemma exceptionalLaw_zero : exceptionalLaw.v 0 = exceptionalX := rfl
lemma exceptionalLaw_one : exceptionalLaw.v 1 = exceptionalY := rfl
lemma exceptionalLaw_two : exceptionalLaw.v 2 = 1 - exceptionalX - exceptionalY := rfl

/-- The exceptional table at i.i.d. law `(x,y,1-x-y)` realizes the moments of
equation (10). -/
lemma exceptional_iid_moments (x y : ℝ) (q : Fin 3 → ℝ)
    (hq0 : q 0 = x) (hq1 : q 1 = y) (hq2 : q 2 = 1 - x - y) :
    (detMoments DetTriangle.exceptional q q q).M1 = exceptionalM1 x y ∧
    (detMoments DetTriangle.exceptional q q q).M2 = exceptionalM2 x y ∧
    (detMoments DetTriangle.exceptional q q q).M3 = exceptionalM3 x y := by
  have hgrid : ∀ (a b : Fin 3), DetTriangle.exceptionalTable a b =
      (if (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨ (a = 1 ∧ b = 1) then (1:ℝ) else -1) := by
    intros; rfl
  refine ⟨?_, ?_, ?_⟩
  · simp only [detMoments, DetTriangle.exceptional]
    repeat rw [Fin.sum_univ_three]
    simp only [DetTriangle.exceptionalTable_zero_zero, DetTriangle.exceptionalTable_zero_one,
      DetTriangle.exceptionalTable_zero_two, DetTriangle.exceptionalTable_one_zero,
      DetTriangle.exceptionalTable_one_one, DetTriangle.exceptionalTable_one_two,
      DetTriangle.exceptionalTable_two_zero, DetTriangle.exceptionalTable_two_one,
      DetTriangle.exceptionalTable_two_two, hq0, hq1, hq2, exceptionalM1]
    ring
  · simp only [detMoments, DetTriangle.exceptional]
    repeat rw [Fin.sum_univ_three]
    simp only [DetTriangle.exceptionalTable_zero_zero, DetTriangle.exceptionalTable_zero_one,
      DetTriangle.exceptionalTable_zero_two, DetTriangle.exceptionalTable_one_zero,
      DetTriangle.exceptionalTable_one_one, DetTriangle.exceptionalTable_one_two,
      DetTriangle.exceptionalTable_two_zero, DetTriangle.exceptionalTable_two_one,
      DetTriangle.exceptionalTable_two_two, hq0, hq1, hq2, exceptionalM2]
    ring
  · simp only [detMoments, DetTriangle.exceptional]
    repeat rw [Fin.sum_univ_three]
    simp only [DetTriangle.exceptionalTable_zero_zero, DetTriangle.exceptionalTable_zero_one,
      DetTriangle.exceptionalTable_zero_two, DetTriangle.exceptionalTable_one_zero,
      DetTriangle.exceptionalTable_one_one, DetTriangle.exceptionalTable_one_two,
      DetTriangle.exceptionalTable_two_zero, DetTriangle.exceptionalTable_two_one,
      DetTriangle.exceptionalTable_two_two, hq0, hq1, hq2, exceptionalM3]
    ring

lemma exceptionalM1_x : exceptionalM1 exceptionalX exceptionalY = 0 := by
  have hy := exceptionalY_ne
  unfold exceptionalX exceptionalM1
  field_simp [hy]
  ring

lemma exceptionalM3_x : exceptionalM3 exceptionalX exceptionalY = 0 := by
  have hy := exceptionalY_ne
  have hp := exceptionalY_eq
  unfold exceptionalM3 exceptionalX exceptionalPoly at *
  field_simp [hy] at *
  nlinarith

lemma exceptionalM2_x : exceptionalM2 exceptionalX exceptionalY
    = 1 / exceptionalY + 2 * exceptionalY - 3 := by
  have hy := exceptionalY_ne
  have hp := exceptionalY_eq
  unfold exceptionalM2 exceptionalX exceptionalPoly at *
  field_simp [hy] at *
  nlinarith

lemma exceptionalM2_gt : (1:ℝ) / exceptionalY + 2 * exceptionalY - 3 > nineTwentyFifths := by
  have hy0 := exceptionalY_pos
  have h1 : (1:ℝ) / exceptionalY > 1 / ((3862:ℝ) / 10000) :=
    one_div_lt_one_div_of_lt hy0 exceptionalY_hi
  have h2 : (2:ℝ) * exceptionalY > 2 * ((3861:ℝ) / 10000) := by
    linarith [exceptionalY_lo]
  have h3 : (1:ℝ) / ((3862:ℝ) / 10000) + 2 * ((3861:ℝ) / 10000) - 3 > 9 / 25 := by
    norm_num
  have h4 : (1:ℝ) / exceptionalY + 2 * exceptionalY - 3 > 9 / 25 := by linarith
  have h5 : (9:ℝ) / 25 = nineTwentyFifths := rfl
  rwa [h5] at h4

/-- The exceptional table admits a feasible point with `M1 = M3 = 0` and
`M2 > 9/25`.  Hence `GapHolds` fails on the orbit of (6). -/
theorem not_gapHolds_exceptional : ¬ GapHolds DetTriangle.exceptional := by
  intro h
  have hm := exceptional_iid_moments exceptionalX exceptionalY
    (fun i => (exceptionalLaw : Fin 3 → ℝ) i)
    exceptionalLaw_zero exceptionalLaw_one exceptionalLaw_two
  have h1 : (detMoments' DetTriangle.exceptional exceptionalLaw exceptionalLaw exceptionalLaw).M1 = 0 := by
    rw [detMoments'_eq_detMoments]
    exact hm.1.trans exceptionalM1_x
  have h3 : (detMoments' DetTriangle.exceptional exceptionalLaw exceptionalLaw exceptionalLaw).M3 = 0 := by
    rw [detMoments'_eq_detMoments]
    exact hm.2.2.trans exceptionalM3_x
  have h2 := h exceptionalLaw exceptionalLaw exceptionalLaw h1 h3
  have h2' : (detMoments' DetTriangle.exceptional exceptionalLaw exceptionalLaw exceptionalLaw).M2
      = 1 / exceptionalY + 2 * exceptionalY - 3 := by
    rw [detMoments'_eq_detMoments]
    exact hm.2.1.trans exceptionalM2_x
  rw [h2'] at h2
  exact not_lt_of_ge h2 exceptionalM2_gt

/-! ## Invariance of `GapHolds` under global output flip -/

/-- Global output flip negates `M1` and `M3` and preserves `M2`. -/
lemma detMoments_flipAll (T : DetTriangle) (qx qy qz : Fin 3 → ℝ) :
    (detMoments (flipAll T) qx qy qz).M1 = -(detMoments T qx qy qz).M1 ∧
    (detMoments (flipAll T) qx qy qz).M2 = (detMoments T qx qy qz).M2 ∧
    (detMoments (flipAll T) qx qy qz).M3 = -(detMoments T qx qy qz).M3 := by
  simp only [detMoments, flipAll, RespTable.flip]
  refine ⟨?_, ?_, ?_⟩
  · repeat rw [Fin.sum_univ_three]
    ring
  · repeat rw [Fin.sum_univ_three]
    ring
  · repeat rw [Fin.sum_univ_three]
    ring

lemma gapHolds_flipAll {T : DetTriangle} (h : GapHolds T) : GapHolds (flipAll T) := by
  intro qx qy qz h1 h3
  have hM := detMoments_flipAll T (fun i => qx i) (fun i => qy i) (fun i => qz i)
  have h1e : (detMoments' (flipAll T) qx qy qz).M1
      = (detMoments (flipAll T) (fun i => qx i) (fun i => qy i) (fun i => qz i)).M1 := rfl
  have h3e : (detMoments' (flipAll T) qx qy qz).M3
      = (detMoments (flipAll T) (fun i => qx i) (fun i => qy i) (fun i => qz i)).M3 := rfl
  rw [h1e, hM.1] at h1
  rw [h3e, hM.2.2] at h3
  have h1T : (detMoments T (fun i => qx i) (fun i => qy i) (fun i => qz i)).M1 = 0 :=
    neg_eq_zero.mp h1
  have h3T : (detMoments T (fun i => qx i) (fun i => qy i) (fun i => qz i)).M3 = 0 :=
    neg_eq_zero.mp h3
  have h2T := h qx qy qz (by rwa [detMoments'_eq_detMoments]) (by rwa [detMoments'_eq_detMoments])
  have h2e : (detMoments' (flipAll T) qx qy qz).M2
      = (detMoments (flipAll T) (fun i => qx i) (fun i => qy i) (fun i => qz i)).M2 := rfl
  rw [h2e, hM.2.1]
  rwa [detMoments'_eq_detMoments] at h2T

lemma RespTable.flip_flip (T : RespTable) : T.flip.flip = T := by
  rcases T with ⟨f, legal⟩
  show ({ f := fun j k => -(-f j k), legal := _ } : RespTable) = ⟨f, legal⟩
  congr 1
  funext j k
  ring

lemma flipAll_flipAll (T : DetTriangle) : flipAll (flipAll T) = T := by
  rcases T with ⟨A, B, C⟩
  simp only [flipAll]
  rw [RespTable.flip_flip, RespTable.flip_flip, RespTable.flip_flip]

lemma gapHolds_flipAll_iff {T : DetTriangle} :
    GapHolds (flipAll T) ↔ GapHolds T := by
  constructor
  · intro h
    have h2 := gapHolds_flipAll h
    rwa [flipAll_flipAll] at h2
  · exact gapHolds_flipAll

/-- The exceptional orbit is closed under the symmetry group; any table in it
is a symmetry image of (6) by definition of `inExceptionalOrbit`. -/
lemma inExceptionalOrbit_def (T : DetTriangle) :
    inExceptionalOrbit T ↔ ∃ g : Symmetry, Symmetry.apply g DetTriangle.exceptional = T :=
  Iff.rfl

/-! ## Closing note on Lemma 5

`certificate_bound`, `bisect_covers`, `certTree_sound` and
`gapHolds_of_certTree` prove that any deterministic ternary response table
admitting a valid certificate tree satisfies the finite gap `M2 ≤ 9/25`
whenever `M1 = M3 = 0`.  `not_gapHolds_exceptional` shows that the exceptional
table of (6) — hence its entire symmetry orbit — violates that bound at an
explicit optimizer, so Lemma 5 *must* exclude that orbit.

The paper's computer-assisted step is the construction of certificate trees for
the other 61871 symmetry orbits (Appendix A, exact integer arithmetic,
`PASS orbits=61872 certified=61871`).  That enumeration is external to Lean and
is **not** asserted here as an axiom. The standalone run is evidence about
the supplied C++ program. It does not close the exhaustive Lean obligation;
Lemma 5 remains partial until all orbit coverage and certificates are checked
inside the trusted proof system.
-/

end Paper15
