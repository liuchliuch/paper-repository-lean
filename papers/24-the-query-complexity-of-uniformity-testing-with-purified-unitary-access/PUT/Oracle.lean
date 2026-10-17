import PUT.Basic

/-!
# Phase-randomized purifications and reflection oracles

Paper 24, (2)–(3): `|v(p,θ)⟩ = ∑ √(p_i/M) e^{iθ_ij}|i,j⟩`,
`|s_v⟩ = (|⊥⟩+|v⟩)/√2`, `U_v = 2|s_v⟩⟨s_v| - I`.

We realize the finite-dimensional Hilbert spaces as `ℂ`-valued functions on
finite index types and prove the algebraic identities of the reflection:
`‖v‖=1`, `⟨s|s⟩=1`, `U²=I`, `U|⊥⟩=|v⟩`, Hermiticity, and the block form
`U = [[0, V†],[V, VV†-I]]` relative to `⊥ ⊕ ℋ`.  The orthogonal-garbage
embedding `|i,j⟩ ↦ |i⟩|i⟩|j⟩` is injective, hence isometric on the span of
the basis states.
-/

noncomputable section
open scoped ComplexConjugate
set_option linter.unusedVariables false
namespace PUT

/-- Label index. -/
abbrev Label (d : ℕ) := Fin d

/-- Garbage coordinate. -/
abbrev Garbage (M : ℕ) := Fin M

/-- Amplitude of `|v(p,θ)⟩` at coordinate `(i,j)`. -/
def vAmplitude (p : Fin d → ℝ) (M : ℕ) (i : Fin d) (j : Fin M) (θ : Fin d → Fin M → ℝ) : ℂ :=
  Complex.ofReal (Real.sqrt (p i / M)) * Complex.exp (Complex.I * θ i j)

/-- Norm-squared of the prepared vector (should be `∑ p_i = 1`). -/
def vNormSq (p : Fin d → ℝ) (M : ℕ) : ℝ := ∑ i, p i

/-- Reflection-oracle block data relative to `⊥ ⊕ ℋ`. -/
structure ReflectionData (d M : ℕ) where
  p : Fin d → ℝ
  θ : Fin d → Fin M → ℝ
  sum_p : ∑ i, p i = 1
  p_nonneg : ∀ i, 0 ≤ p i

/-- Orthogonal-garbage variant obtained by `|i,j⟩ ↦ |i⟩|i⟩|j⟩`. -/
def garbageEmbed (d M : ℕ) (i : Fin d) (j : Fin M) : Fin d × Fin d × Fin M := (i, i, j)

/-! ## Concrete Hilbert-space model -/

/-- The purification `|v(p,θ)⟩` as a `ℂ`-valued function on `Fin d × Fin M`. -/
def vVec {d : ℕ} (p : Fin d → ℝ) (M : ℕ) (θ : Fin d → Fin M → ℝ) :
    Fin d × Fin M → ℂ :=
  fun ij => vAmplitude p M ij.1 ij.2 θ

/-- Conditional garbage state for label `i`: `M^{-1/2} ∑_j e^{iθ_ij}|j⟩`. -/
def garbageVec {d : ℕ} (M : ℕ) (θ : Fin d → Fin M → ℝ) (i : Fin d) : Fin M → ℂ :=
  fun j => Complex.ofReal (1 / Real.sqrt M) * Complex.exp (Complex.I * θ i j)

/-- Extended Hilbert space `ℋ' = ℂ|⊥⟩ ⊕ ℋ`, modeled as `Unit ⊕ (Fin d × Fin M)`. -/
abbrev HQ (d M : ℕ) := Sum Unit (Fin d × Fin M)

/-- The designated zero state `|⊥⟩`. -/
def botVec {d M : ℕ} : HQ d M → ℂ
  | Sum.inl _ => 1
  | Sum.inr _ => 0

/-- `|v⟩` embedded into `ℋ'` (supported on the `ℋ` summand). -/
def vExt {d : ℕ} (p : Fin d → ℝ) (M : ℕ) (θ : Fin d → Fin M → ℝ) : HQ d M → ℂ
  | Sum.inl _ => 0
  | Sum.inr ij => vVec p M θ ij

/-- `|s_v⟩ = (|⊥⟩+|v⟩)/√2`. -/
def sVec {d : ℕ} (p : Fin d → ℝ) (M : ℕ) (θ : Fin d → Fin M → ℝ) : HQ d M → ℂ
  | Sum.inl _ => Complex.ofReal (1 / Real.sqrt 2)
  | Sum.inr ij => Complex.ofReal (1 / Real.sqrt 2) * vVec p M θ ij

/-- A general state of `ℋ'` split as `c|⊥⟩ + |h⟩`. -/
def splitVec {d M : ℕ} (c : ℂ) (h : Fin d × Fin M → ℂ) : HQ d M → ℂ
  | Sum.inl _ => c
  | Sum.inr ij => h ij

/-- Standard sesquilinear inner product on `ι → ℂ`, conjugate-linear in the
first argument (the paper's convention). -/
def cdot {ι : Type*} [Fintype ι] (x y : ι → ℂ) : ℂ :=
  ∑ i, conj (x i) * y i

/-- Reflection `U_s = 2|s⟩⟨s| - I` as a map on `ι → ℂ`. -/
def reflectVec {ι : Type*} [Fintype ι] (s x : ι → ℂ) : ι → ℂ :=
  fun k => 2 * cdot s x * s k - x k

/-! ## Elementary scalar identities -/

theorem inv_sqrt_two_mul : (1 / Real.sqrt 2 : ℝ) * (1 / Real.sqrt 2) = 1 / 2 := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have h : Real.sqrt 2 * Real.sqrt 2 = (2:ℝ) := Real.mul_self_sqrt (by norm_num)
  field_simp [ne_of_gt hs]
  nlinarith

theorem conj_ofReal_ofReal {r : ℝ} : conj (Complex.ofReal r) = Complex.ofReal r :=
  Complex.conj_ofReal r

theorem exp_I_theta_normSq (θ : ℝ) :
    Complex.normSq (Complex.exp (Complex.I * θ)) = 1 := by
  have hre : (Complex.I * (θ : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  rw [Complex.normSq_eq_norm_sq, Complex.norm_exp, hre, Real.exp_zero, one_pow]

theorem conj_mul_self (z : ℂ) : conj z * z = (Complex.normSq z : ℂ) := by
  rw [mul_comm, Complex.mul_conj]

theorem cdot_apply {ι : Type*} [Fintype ι] (s x : ι → ℂ) :
    cdot s x = ∑ i, conj (s i) * x i := rfl

theorem reflectVec_apply {ι : Type*} [Fintype ι] (s x : ι → ℂ) (k : ι) :
    reflectVec s x k = 2 * cdot s x * s k - x k := rfl

/-! ## Inner-product algebra of the reflection -/

/-- `⟨s|U_s x⟩ = ⟨s|x⟩` when `⟨s|s⟩=1`: the reflection fixes the `s`-component. -/
theorem cdot_s_reflect {ι : Type*} [Fintype ι] (s x : ι → ℂ) (hs : cdot s s = 1) :
    cdot s (reflectVec s x) = cdot s x := by
  have h2 : ∀ k, conj (s k) * (2 * cdot s x * s k - x k)
      = 2 * cdot s x * (conj (s k) * s k) - conj (s k) * x k := by
    intro k; ring
  have hsum : (∑ k, conj (s k) * (2 * cdot s x * s k - x k))
      = 2 * cdot s x * ∑ k, conj (s k) * s k - ∑ k, conj (s k) * x k := by
    rw [Finset.sum_congr rfl (fun k _ => h2 k), Finset.sum_sub_distrib]
    have h4 : ∑ k, 2 * cdot s x * (conj (s k) * s k)
        = 2 * cdot s x * ∑ k, conj (s k) * s k := by
      rw [← Finset.mul_sum]
    rw [h4]
  unfold cdot
  show (∑ k, conj (s k) * reflectVec s x k) = _
  simp only [reflectVec_apply]
  rw [hsum]
  have hss : ∑ i, conj (s i) * s i = cdot s s := rfl
  have hxx : ∑ i, conj (s i) * x i = cdot s x := rfl
  rw [hss, hxx, hs, mul_one]
  ring

/-- `U_s² = I` as a formal consequence of `|s⟩⟨s|` being a projector
(`⟨s|s⟩ = 1`). -/
theorem reflect_sq {ι : Type*} [Fintype ι] (s x : ι → ℂ) (hs : cdot s s = 1) :
    reflectVec s (reflectVec s x) = x := by
  have h : cdot s (reflectVec s x) = cdot s x := cdot_s_reflect s x hs
  funext k
  rw [reflectVec_apply, reflectVec_apply, h]
  ring

/-- The reflection is Hermitian: `⟨U_s x|y⟩ = ⟨x|U_s y⟩`. -/
theorem reflect_hermitian {ι : Type*} [Fintype ι] (s x y : ι → ℂ) :
    cdot (reflectVec s x) y = cdot x (reflectVec s y) := by
  have hxs : ∀ k, conj (2 * cdot s x * s k - x k) * y k
      = 2 * conj (cdot s x) * (conj (s k) * y k) - conj (x k) * y k := by
    intro k
    have hc2 : conj (2 : ℂ) = 2 := by norm_num [map_ofNat]
    simp only [map_sub, map_mul, hc2]
    ring
  have hys : ∀ k, conj (x k) * (2 * cdot s y * s k - y k)
      = 2 * cdot s y * (conj (x k) * s k) - conj (x k) * y k := by
    intro k; ring
  unfold cdot
  show (∑ k, conj (reflectVec s x k) * y k) = (∑ k, conj (x k) * reflectVec s y k)
  simp only [reflectVec_apply]
  rw [Finset.sum_congr rfl (fun k _ => hxs k), Finset.sum_congr rfl (fun k _ => hys k)]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have h1 : ∑ k, 2 * conj (cdot s x) * (conj (s k) * y k)
      = 2 * conj (cdot s x) * ∑ k, conj (s k) * y k := by
    rw [← Finset.mul_sum]
  have h2 : ∑ k, 2 * cdot s y * (conj (x k) * s k)
      = 2 * cdot s y * ∑ k, conj (x k) * s k := by
    rw [← Finset.mul_sum]
  rw [h1, h2]
  have hcs : ∑ k, conj (x k) * s k = conj (∑ k, conj (s k) * x k) := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [map_mul, starRingEnd_self_apply]
    ring
  rw [hcs]
  -- Both sides are `2 * conj(⟨s,x⟩) * ⟨s,y⟩ - ⟨x,y⟩` up to commutativity.
  change 2 * conj (cdot s x) * cdot s y - cdot x y
    = 2 * cdot s y * conj (cdot s x) - cdot x y
  ring

/-! ## Norm identities for the purification -/

theorem normSq_vAmplitude {d : ℕ} (p : Fin d → ℝ) (M : ℕ) (θ : Fin d → Fin M → ℝ)
    (i : Fin d) (j : Fin M) (hM : 0 < M) (hp : 0 ≤ p i) :
    Complex.normSq (vAmplitude p M i j θ) = p i / M := by
  unfold vAmplitude
  rw [Complex.normSq_mul, Complex.normSq_ofReal, exp_I_theta_normSq, mul_one]
  have hnn : 0 ≤ (p i / M : ℝ) := div_nonneg hp (Nat.cast_nonneg M)
  exact Real.mul_self_sqrt hnn

theorem cnormSq_vVec {d : ℕ} (p : Fin d → ℝ) (M : ℕ) (θ : Fin d → Fin M → ℝ)
    (hM : 0 < M) (hp : ∀ i, 0 ≤ p i) :
    (∑ ij : Fin d × Fin M, Complex.normSq (vVec p M θ ij)) = ∑ i : Fin d, p i := by
  have hprod : (∑ ij : Fin d × Fin M, Complex.normSq (vVec p M θ ij))
      = ∑ i : Fin d, ∑ j : Fin M, Complex.normSq (vAmplitude p M i j θ) :=
    Fintype.sum_prod_type _
  rw [hprod]
  have hterm : ∀ i j, Complex.normSq (vAmplitude p M i j θ) = p i / M :=
    fun i j => normSq_vAmplitude p M θ i j hM (hp i)
  simp only [hterm]
  have hrow : ∀ i : Fin d, (∑ j : Fin M, p i / M) = p i := by
    intro i
    rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    have hne : (M : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hM)
    field_simp
  simp only [hrow]

/-- `‖v(p,θ)‖² = ∑ p_i = vNormSq p M`. -/
theorem vVec_normSq {d : ℕ} (p : Fin d → ℝ) (M : ℕ) (θ : Fin d → Fin M → ℝ)
    (hM : 0 < M) (hp : ∀ i, 0 ≤ p i) :
    (∑ ij : Fin d × Fin M, Complex.normSq (vVec p M θ ij)) = vNormSq p M :=
  cnormSq_vVec p M θ hM hp

/-- When `p` is a probability vector, `‖v‖² = 1`. -/
theorem vVec_normSq_one (d M : ℕ) (data : ReflectionData d M) (hM : 0 < M) :
    (∑ ij : Fin d × Fin M, Complex.normSq (vVec data.p M data.θ ij)) = 1 := by
  rw [cnormSq_vVec data.p M data.θ hM data.p_nonneg, data.sum_p]

/-- Conditional garbage for label `i` has norm 1. -/
theorem garbageVec_normSq {d : ℕ} (M : ℕ) (θ : Fin d → Fin M → ℝ) (i : Fin d)
    (hM : 0 < M) :
    (∑ j : Fin M, Complex.normSq (garbageVec M θ i j)) = 1 := by
  have hterm : ∀ j, Complex.normSq (garbageVec M θ i j) = 1 / M := by
    intro j
    unfold garbageVec
    rw [Complex.normSq_mul, Complex.normSq_ofReal, exp_I_theta_normSq, mul_one]
    have hnn : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
    have hpos : 0 < (M : ℝ) := by exact_mod_cast hM
    have hs : 0 < Real.sqrt M := Real.sqrt_pos.2 hpos
    have hsq : (1 / Real.sqrt M) * (1 / Real.sqrt M) = 1 / M := by
      have h : Real.sqrt M * Real.sqrt M = (M:ℝ) := Real.mul_self_sqrt hnn
      field_simp [ne_of_gt hs, ne_of_gt hpos]
      nlinarith
    exact hsq
  simp only [hterm]
  rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  have hne : (M : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hM)
  field_simp

/-! ## The purified state `|s_v⟩` and the reflection `U_v` -/

theorem sVec_eq {d : ℕ} (p : Fin d → ℝ) (M : ℕ) (θ : Fin d → Fin M → ℝ) (q : HQ d M) :
    sVec p M θ q
      = Complex.ofReal (1 / Real.sqrt 2) * (botVec q + vExt p M θ q) := by
  cases q with
  | inl u => simp [sVec, botVec, vExt]
  | inr ij => simp [sVec, botVec, vExt]

theorem ofReal_half : Complex.ofReal (1 / 2) = (1 / 2 : ℂ) := by
  rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]

theorem sVec_inl {d : ℕ} (p : Fin d → ℝ) (M : ℕ) (θ : Fin d → Fin M → ℝ) (u : Unit) :
    sVec p M θ (Sum.inl u) = Complex.ofReal (1 / Real.sqrt 2) := rfl

theorem sVec_inr {d : ℕ} (p : Fin d → ℝ) (M : ℕ) (θ : Fin d → Fin M → ℝ)
    (ij : Fin d × Fin M) :
    sVec p M θ (Sum.inr ij) = Complex.ofReal (1 / Real.sqrt 2) * vVec p M θ ij := rfl

theorem two_mul_inv_sqrt_two_sq :
    (2:ℂ) * Complex.ofReal (1 / Real.sqrt 2) * Complex.ofReal (1 / Real.sqrt 2) = 1 := by
  have h : (2:ℂ) * Complex.ofReal (1 / Real.sqrt 2) = Complex.ofReal (2 * (1 / Real.sqrt 2)) := by
    rw [Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [h, ← Complex.ofReal_mul]
  have : (2:ℝ) * (1 / Real.sqrt 2) * (1 / Real.sqrt 2) = 1 := by
    nlinarith [inv_sqrt_two_mul]
  rw [this, Complex.ofReal_one]

theorem inv_sqrt_two_sq :
    Complex.ofReal (1 / Real.sqrt 2) * Complex.ofReal (1 / Real.sqrt 2) = (1 / 2 : ℂ) := by
  rw [← Complex.ofReal_mul, inv_sqrt_two_mul, ofReal_half]

theorem ofReal_sum_normSq {d : ℕ} (p : Fin d → ℝ) (M : ℕ) (θ : Fin d → Fin M → ℝ) :
    (∑ ij : Fin d × Fin M, (Complex.normSq (vVec p M θ ij) : ℂ))
      = ((∑ ij : Fin d × Fin M, Complex.normSq (vVec p M θ ij)) : ℂ) := rfl

/-- `⟨s|s⟩ = 1` when `‖v‖ = 1`. -/
theorem sVec_dot_self {d : ℕ} (p : Fin d → ℝ) (M : ℕ) (θ : Fin d → Fin M → ℝ)
    (hM : 0 < M) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    cdot (sVec p M θ) (sVec p M θ) = 1 := by
  unfold cdot
  have hsplit : (∑ q : HQ d M, conj (sVec p M θ q) * sVec p M θ q)
      = (∑ u : Unit, conj (sVec p M θ (Sum.inl u)) * sVec p M θ (Sum.inl u))
        + ∑ ij : Fin d × Fin M,
            conj (sVec p M θ (Sum.inr ij)) * sVec p M θ (Sum.inr ij) :=
    Fintype.sum_sum_type _
  rw [hsplit]
  have hbot : (∑ u : Unit, conj (sVec p M θ (Sum.inl u)) * sVec p M θ (Sum.inl u))
      = (1 / 2 : ℂ) := by
    simp only [sVec_inl]
    rw [Fintype.sum_unique, Complex.conj_ofReal, inv_sqrt_two_sq]
  rw [hbot]
  have hv : (∑ ij : Fin d × Fin M, conj (sVec p M θ (Sum.inr ij)) * sVec p M θ (Sum.inr ij))
      = (1 / 2 : ℂ) := by
    have h1 : ∀ ij, conj (sVec p M θ (Sum.inr ij)) * sVec p M θ (Sum.inr ij)
        = Complex.ofReal (1 / Real.sqrt 2) * Complex.ofReal (1 / Real.sqrt 2)
            * (conj (vVec p M θ ij) * vVec p M θ ij) := by
      intro ij
      rw [sVec_inr, map_mul, Complex.conj_ofReal]
      ring
    rw [Finset.sum_congr rfl (fun ij _ => h1 ij)]
    have h2 : ∀ ij, conj (vVec p M θ ij) * vVec p M θ ij
        = (Complex.normSq (vVec p M θ ij) : ℂ) :=
      fun ij => conj_mul_self _
    have h4 : ∑ ij, (conj (vVec p M θ ij) * vVec p M θ ij)
        = ((∑ ij, Complex.normSq (vVec p M θ ij)) : ℂ) := by
      simp [h2]
    have h5 : (∑ ij, Complex.ofReal (1 / Real.sqrt 2) * Complex.ofReal (1 / Real.sqrt 2)
        * (conj (vVec p M θ ij) * vVec p M θ ij))
        = Complex.ofReal (1 / Real.sqrt 2) * Complex.ofReal (1 / Real.sqrt 2)
            * ((∑ ij, Complex.normSq (vVec p M θ ij)) : ℂ) := by
      have h6 : ∑ ij, Complex.ofReal (1 / Real.sqrt 2) * Complex.ofReal (1 / Real.sqrt 2)
          * (conj (vVec p M θ ij) * vVec p M θ ij)
          = Complex.ofReal (1 / Real.sqrt 2) * Complex.ofReal (1 / Real.sqrt 2)
              * ∑ ij, (conj (vVec p M θ ij) * vVec p M θ ij) := by
        rw [← Finset.mul_sum]
      rw [h6, h4]
    rw [h5]
    -- The complex sum of coerced norms is the coercion of the real sum.
    rw [← Complex.ofReal_sum]
    rw [cnormSq_vVec p M θ hM hp, hsum, Complex.ofReal_one,
      inv_sqrt_two_sq, mul_one]
  rw [hv]
  norm_num

/-- `U_v|⊥⟩ = |v⟩`. -/
theorem reflect_bot {d : ℕ} (p : Fin d → ℝ) (M : ℕ) (θ : Fin d → Fin M → ℝ)
    (hM : 0 < M) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    reflectVec (sVec p M θ) botVec = vExt p M θ := by
  have hs : cdot (sVec p M θ) botVec = Complex.ofReal (1 / Real.sqrt 2) := by
    unfold cdot
    have hsplit : (∑ q : HQ d M, conj (sVec p M θ q) * botVec q)
        = (∑ u : Unit, conj (sVec p M θ (Sum.inl u)) * botVec (Sum.inl u))
          + ∑ ij : Fin d × Fin M,
              conj (sVec p M θ (Sum.inr ij)) * botVec (Sum.inr ij) :=
      Fintype.sum_sum_type _
    rw [hsplit]
    have h0 : (∑ ij : Fin d × Fin M, conj (sVec p M θ (Sum.inr ij)) * botVec (Sum.inr ij)) = 0 := by
      simp [botVec]
    rw [h0, add_zero]
    simp only [sVec_inl, botVec]
    rw [Fintype.sum_unique, Complex.conj_ofReal, mul_one]
  funext q
  cases q with
  | inl u =>
    have h1 : reflectVec (sVec p M θ) botVec (Sum.inl u)
        = 2 * cdot (sVec p M θ) botVec * sVec p M θ (Sum.inl u) - botVec (Sum.inl u) :=
      rfl
    rw [h1, hs, sVec_inl]
    have h2 : (2:ℂ) * Complex.ofReal (1 / Real.sqrt 2) * Complex.ofReal (1 / Real.sqrt 2) = 1 :=
      two_mul_inv_sqrt_two_sq
    rw [h2]
    simp [botVec, vExt]
  | inr ij =>
    have h1 : reflectVec (sVec p M θ) botVec (Sum.inr ij)
        = 2 * cdot (sVec p M θ) botVec * sVec p M θ (Sum.inr ij) - botVec (Sum.inr ij) :=
      rfl
    rw [h1, hs, sVec_inr]
    simp only [botVec, vExt, sub_zero]
    have h2 : (2:ℂ) * Complex.ofReal (1 / Real.sqrt 2) * Complex.ofReal (1 / Real.sqrt 2) = 1 :=
      two_mul_inv_sqrt_two_sq
    conv_lhs => rw [← mul_assoc]
    rw [h2, one_mul]

/-- `U_v` is a Hermitian unitary: `U_v² = I`. -/
theorem reflect_unitary {d : ℕ} (p : Fin d → ℝ) (M : ℕ) (θ : Fin d → Fin M → ℝ)
    (hM : 0 < M) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (x : HQ d M → ℂ) :
    reflectVec (sVec p M θ) (reflectVec (sVec p M θ) x) = x :=
  reflect_sq (sVec p M θ) x (sVec_dot_self p M θ hM hp hsum)

/-- `U_v` is Hermitian on `ℋ'`. -/
theorem reflect_hermitian_sVec {d : ℕ} (p : Fin d → ℝ) (M : ℕ) (θ : Fin d → Fin M → ℝ)
    (x y : HQ d M → ℂ) :
    cdot (reflectVec (sVec p M θ) x) y = cdot x (reflectVec (sVec p M θ) y) :=
  reflect_hermitian (sVec p M θ) x y

/-- Block form of (3): for `x = c|⊥⟩ + |h⟩`,
`U x = ⟨v|h⟩|⊥⟩ ⊕ (c|v⟩ + ⟨v|h⟩|v⟩ - |h⟩)`, i.e.
`U = [[0, V†],[V, VV†-I]]` with `V c = c|v⟩`, `V† h = ⟨v|h⟩`. -/
theorem reflect_block {d : ℕ} (p : Fin d → ℝ) (M : ℕ) (θ : Fin d → Fin M → ℝ)
    (hM : 0 < M) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (c : ℂ) (h : Fin d × Fin M → ℂ) :
    reflectVec (sVec p M θ) (splitVec c h)
      = splitVec (cdot (vVec p M θ) h)
          (fun ij => c * vVec p M θ ij + cdot (vVec p M θ) h * vVec p M θ ij - h ij) := by
  have hs : cdot (sVec p M θ) (splitVec c h)
      = Complex.ofReal (1 / Real.sqrt 2) * (c + cdot (vVec p M θ) h) := by
    unfold cdot
    have hsplit : (∑ q : HQ d M, conj (sVec p M θ q) * splitVec c h q)
        = (∑ u : Unit, conj (sVec p M θ (Sum.inl u)) * splitVec c h (Sum.inl u))
          + ∑ ij : Fin d × Fin M,
              conj (sVec p M θ (Sum.inr ij)) * splitVec c h (Sum.inr ij) :=
      Fintype.sum_sum_type _
    rw [hsplit]
    have h0 : (∑ u : Unit, conj (sVec p M θ (Sum.inl u)) * splitVec c h (Sum.inl u))
        = Complex.ofReal (1 / Real.sqrt 2) * c := by
      simp only [sVec_inl, splitVec]
      rw [Fintype.sum_unique, Complex.conj_ofReal]
    have h1 : (∑ ij : Fin d × Fin M, conj (sVec p M θ (Sum.inr ij)) * splitVec c h (Sum.inr ij))
        = Complex.ofReal (1 / Real.sqrt 2) * cdot (vVec p M θ) h := by
      have hterm : ∀ ij, conj (sVec p M θ (Sum.inr ij)) * splitVec c h (Sum.inr ij)
          = Complex.ofReal (1 / Real.sqrt 2) * (conj (vVec p M θ ij) * h ij) := by
        intro ij
        rw [sVec_inr, map_mul, Complex.conj_ofReal]
        show Complex.ofReal (1 / Real.sqrt 2) * conj (vVec p M θ ij) * h ij
          = Complex.ofReal (1 / Real.sqrt 2) * (conj (vVec p M θ ij) * h ij)
        ring
      rw [Finset.sum_congr rfl (fun ij _ => hterm ij)]
      have : ∑ ij, Complex.ofReal (1 / Real.sqrt 2) * (conj (vVec p M θ ij) * h ij)
          = Complex.ofReal (1 / Real.sqrt 2) * ∑ ij, conj (vVec p M θ ij) * h ij := by
        rw [← Finset.mul_sum]
      rw [this]
      rfl
    rw [h0, h1, mul_add]
    rfl
  funext q
  cases q with
  | inl u =>
    have h1 : reflectVec (sVec p M θ) (splitVec c h) (Sum.inl u)
        = 2 * cdot (sVec p M θ) (splitVec c h) * sVec p M θ (Sum.inl u)
            - splitVec c h (Sum.inl u) := rfl
    rw [h1, hs, sVec_inl, splitVec]
    have h2 : (2:ℂ) * (Complex.ofReal (1 / Real.sqrt 2) * (c + cdot (vVec p M θ) h))
        * Complex.ofReal (1 / Real.sqrt 2) = c + cdot (vVec p M θ) h := by
      have h2a : (2:ℂ) * Complex.ofReal (1 / Real.sqrt 2) * Complex.ofReal (1 / Real.sqrt 2) = 1 :=
        two_mul_inv_sqrt_two_sq
      linear_combination h2a * (c + cdot (vVec p M θ) h)
    rw [h2]
    simp [splitVec]
  | inr ij =>
    have h1 : reflectVec (sVec p M θ) (splitVec c h) (Sum.inr ij)
        = 2 * cdot (sVec p M θ) (splitVec c h) * sVec p M θ (Sum.inr ij)
            - splitVec c h (Sum.inr ij) := rfl
    rw [h1, hs, sVec_inr, splitVec]
    have h2 : (2:ℂ) * (Complex.ofReal (1 / Real.sqrt 2) * (c + cdot (vVec p M θ) h))
        * (Complex.ofReal (1 / Real.sqrt 2) * vVec p M θ ij)
        = (c + cdot (vVec p M θ) h) * vVec p M θ ij := by
      have h2a : (2:ℂ) * Complex.ofReal (1 / Real.sqrt 2) * Complex.ofReal (1 / Real.sqrt 2) = 1 :=
        two_mul_inv_sqrt_two_sq
      linear_combination h2a * (c + cdot (vVec p M θ) h) * vVec p M θ ij
    rw [h2]
    show (c + cdot (vVec p M θ) h) * vVec p M θ ij - h ij
      = c * vVec p M θ ij + cdot (vVec p M θ) h * vVec p M θ ij - h ij
    rw [add_mul]

/-! ## Orthogonal garbage embedding -/

/-- `|i,j⟩ ↦ |i⟩|i⟩|j⟩` is injective, hence extends to an isometry on the
span of the basis states; images of distinct pairs are distinct basis states. -/
theorem garbageEmbed_injective (d M : ℕ) :
    Function.Injective (fun ij : Fin d × Fin M => garbageEmbed d M ij.1 ij.2) := by
  intro ⟨i, j⟩ ⟨i', j'⟩ h
  simp only [garbageEmbed] at h
  injection h

theorem garbageEmbed_ne {d M : ℕ} {ij ij' : Fin d × Fin M}
    (h : ij ≠ ij') :
    (fun ij : Fin d × Fin M => garbageEmbed d M ij.1 ij.2) ij
      ≠ (fun ij : Fin d × Fin M => garbageEmbed d M ij.1 ij.2) ij' :=
  fun he => h (garbageEmbed_injective d M he)

/-- Distinct embedded basis states occupy distinct triples. -/
theorem garbageEmbed_disjoint {d M : ℕ} {ij ij' : Fin d × Fin M}
    (h : ij ≠ ij') :
    (fun ij : Fin d × Fin M => garbageEmbed d M ij.1 ij.2) ij
      ≠ (fun ij : Fin d × Fin M => garbageEmbed d M ij.1 ij.2) ij' :=
  garbageEmbed_ne h

end PUT
