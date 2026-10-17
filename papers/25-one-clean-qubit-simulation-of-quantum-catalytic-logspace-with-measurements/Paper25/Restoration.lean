import Paper25.Norms
import Paper25.Liouville
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Lemma 2: Exact restoration

Let `Ψ : C → WC` be a CPTP map with `Tr_W ∨ Ψ(ρ) = ρ` for every state `ρ` on `C`.
Then there is a state `η` on `W` such that `Ψ(X) = η ⊗ X` for every operator `X`
on `C`; consequently `Ψ` preserves correlations with an inaccessible reference.

Algebraic content formalized here:

* `vec(|i⟩⟨j|) = |i⟩|j|`;
* unitary conjugation has Liouville matrix `G ⊗ conj(G)`;
* equation (3): `S (|ω⟩ ⊗ I_{D²}) = |η⟩ ⊗ I_{D²}`;
* bias identity (4): `(1/D²) Tr[(|ω⟩⟨z| ⊗ I) S] = ⟨z|η⟩`;
* product-form conclusion `Ψ(X) = η ⊗ X` from coefficient comparison.
-/

noncomputable section

open scoped ComplexConjugate

namespace Paper25

/-! ## Vectorization of operators -/

/-- Standard basis matrix `|i⟩⟨j|` on `Fin d`. -/
def basisMat {d : ℕ} (i j : Fin d) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun a b => if a = i ∧ b = j then 1 else 0

lemma basisMat_apply {d : ℕ} (i j a b : Fin d) :
    basisMat i j a b = if a = i ∧ b = j then 1 else 0 :=
  rfl

/-- Vectorization `vec(X)_{(a,b)} = X_{a,b}`; `vec(|i⟩⟨j|) = |i⟩|j|`. -/
def vec {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) : Fin d × Fin d → ℂ :=
  fun p => X p.1 p.2

/-- **`vec` of `|i⟩⟨j|` is `|i⟩|j|`.** -/
theorem vec_basisMat {d : ℕ} (i j a b : Fin d) :
    vec (basisMat i j) (a, b)
      = (if a = i then (1 : ℂ) else 0) * (if b = j then (1 : ℂ) else 0) := by
  simp only [vec, basisMat_apply]
  by_cases ha : a = i <;> by_cases hb : b = j <;> simp [ha, hb]

theorem vec_basisMat_diag {d : ℕ} (i j : Fin d) :
    vec (basisMat i j) (i, j) = 1 := by
  simp [vec_basisMat]

theorem vec_basisMat_off {d : ℕ} (i j a b : Fin d) (h : (a, b) ≠ (i, j)) :
    vec (basisMat i j) (a, b) = 0 := by
  rw [vec_basisMat]
  by_cases ha : a = i
  · by_cases hb : b = j
    · exact absurd (by simp [ha, hb] : (a, b) = (i, j)) h
    · simp [hb]
  · simp [ha]

/-- **Liouville matrix of a unitary conjugation is `G ⊗ conj(G)`.** -/
theorem vec_conj_unitary {d : ℕ} (G X : Matrix (Fin d) (Fin d) ℂ) (a b : Fin d) :
    vec (G * X * G.conjTranspose) (a, b)
      = ∑ p : Fin d × Fin d, unitaryL G (a, b) p * vec X p := by
  classical
  have hL : (G * X * G.conjTranspose) a b
      = ∑ i : Fin d, ∑ j : Fin d, G a i * X i j * star (G b j) := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    conv_lhs => simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
  have hcell : ∀ i j : Fin d,
      unitaryL G (a, b) (i, j) * vec X (i, j) = G a i * X i j * star (G b j) := by
    intro i j
    simp only [unitaryL, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.map_apply, vec]
    show G a i * (starRingEnd ℂ) (G b j) * X i j = G a i * X i j * star (G b j)
    rw [show star (G b j) = (starRingEnd ℂ) (G b j) from rfl]
    ring_nf
  have hR : (∑ p : Fin d × Fin d, unitaryL G (a, b) p * vec X p)
      = ∑ i : Fin d, ∑ j : Fin d, G a i * X i j * star (G b j) := by
    conv_lhs => rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hcell i j
  show (G * X * G.conjTranspose) a b
      = ∑ p : Fin d × Fin d, unitaryL G (a, b) p * vec X p
  rw [hL, hR]

/-! ## Equation (3) and the product form -/

/-- The block column `|ω⟩ ⊗ I_n`, an `(m n) × n` matrix. -/
def kronColId {m n : ℕ} (ω : Fin m → ℂ) : Matrix (Fin m × Fin n) (Fin n) ℂ :=
  Matrix.of fun p j => ω p.1 * (if p.2 = j then (1 : ℂ) else 0)

lemma kronColId_apply {m n : ℕ} (ω : Fin m → ℂ) (p : Fin m × Fin n) (j : Fin n) :
    kronColId ω p j = ω p.1 * (if p.2 = j then (1 : ℂ) else 0) :=
  rfl

/-- The rank-one work operator `|ω⟩⟨z| ⊗ I_n`. -/
def kronRankOneId {m n : ℕ} (ω z : Fin m → ℂ) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  Matrix.of fun p q => ω p.1 * star (z q.1) * (if p.2 = q.2 then (1 : ℂ) else 0)

lemma kronRankOneId_apply {m n : ℕ} (ω z : Fin m → ℂ)
    (p q : Fin m × Fin n) :
    kronRankOneId ω z p q = ω p.1 * star (z q.1) * (if p.2 = q.2 then (1 : ℂ) else 0) :=
  rfl

/-- The vector `|ω⟩ ⊗ x` on the doubled work-catalyst register. -/
def kronVec {m n : ℕ} (ω : Fin m → ℂ) (x : Fin n → ℂ) : Fin m × Fin n → ℂ :=
  fun p => ω p.1 * x p.2

/-- **Equation (3).** `S (|ω⟩ ⊗ I_{D²}) = |η⟩ ⊗ I_{D²}`. -/
def ExactRestoration {m n : ℕ} (S : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)
    (ω η : Fin m → ℂ) : Prop :=
  S * kronColId ω = kronColId η

/-- The catalyst-coordinate inner product `⟨z|η⟩`. -/
def cinner {m : ℕ} (z η : Fin m → ℂ) : ℂ :=
  ∑ i, star (z i) * η i

lemma kronColId_mulVec {m n : ℕ} (ω : Fin m → ℂ) (x : Fin n → ℂ) :
    Matrix.mulVec (kronColId (n := n) ω) x = kronVec ω x := by
  classical
  funext p
  simp only [Matrix.mulVec, dotProduct, kronColId_apply, kronVec]
  have h : ∀ j : Fin n,
      (ω p.1 * (if p.2 = j then (1 : ℂ) else 0)) * x j
        = if j = p.2 then ω p.1 * x j else 0 := by
    intro j
    by_cases hp : j = p.2
    · subst hp
      simp
    · have hp' : ¬(p.2 = j) := fun e => hp e.symm
      simp [hp, hp']
  rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_ite_eq']
  simp

/-- Equation (3) is an identity on all catalyst operator coordinates. -/
theorem exactRestoration_mulVec {m n : ℕ}
    {S : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ} {ω η : Fin m → ℂ}
    (h : ExactRestoration S ω η) (x : Fin n → ℂ) :
    Matrix.mulVec S (kronVec ω x) = kronVec η x := by
  classical
  rw [← kronColId_mulVec ω x, ← kronColId_mulVec η x]
  show Matrix.mulVec S (Matrix.mulVec (kronColId ω) x)
      = Matrix.mulVec (kronColId η) x
  rw [Matrix.mulVec_mulVec, h]

/-- **Product-form action.** `S (|ω⟩⊗x) = |η⟩⊗x` for every catalyst coordinate. -/
theorem lemma_2_product_action {m n : ℕ}
    {S : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ} {ω η : Fin m → ℂ}
    (h : ExactRestoration S ω η) (x : Fin n → ℂ) :
    Matrix.mulVec S (kronVec ω x) = kronVec η x :=
  exactRestoration_mulVec h x

/-- The product-form Liouville matrix `(|η⟩ ⊗ I)(⟨ω| ⊗ I) = |η⟩⟨ω| ⊗ I`. -/
def productLiouville {m n : ℕ} (η ω : Fin m → ℂ) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  kronColId η * (kronColId ω).conjTranspose

/-- `(|η⟩ ⊗ I)(⟨ω| ⊗ I) = |η⟩⟨ω| ⊗ I`. -/
theorem productLiouville_eq {m n : ℕ} (η ω : Fin m → ℂ) :
    productLiouville (n := n) η ω = kronRankOneId (n := n) η ω := by
  classical
  ext p q
  simp only [productLiouville, Matrix.mul_apply, Matrix.conjTranspose_apply,
    kronColId_apply, kronRankOneId_apply]
  have h : ∀ j : Fin n,
      (η p.1 * (if p.2 = j then (1 : ℂ) else 0))
        * star (ω q.1 * (if q.2 = j then (1 : ℂ) else 0))
      = if p.2 = j ∧ q.2 = j then η p.1 * star (ω q.1) else 0 := by
    intro j
    by_cases hp : p.2 = j <;> by_cases hq : q.2 = j <;> simp [hp, hq]
  rw [Finset.sum_congr rfl fun j _ => h j]
  have hsum : (∑ j : Fin n, if p.2 = j ∧ q.2 = j then η p.1 * star (ω q.1) else 0)
      = if p.2 = q.2 then η p.1 * star (ω q.1) else 0 := by
    by_cases hpq : p.2 = q.2
    · have hsum' : (∑ j : Fin n, if p.2 = j ∧ q.2 = j then η p.1 * star (ω q.1) else 0)
        = η p.1 * star (ω q.1) := by
        rw [Finset.sum_eq_single p.2]
        · rw [hpq]
          simp
        · intro j _ hj
          exact if_neg (fun hcon => hj hcon.1.symm)
        · intro hp
          exact absurd (Finset.mem_univ p.2) hp
      rw [hsum', if_pos hpq]
    · rw [if_neg hpq]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hp : p.2 = j
      · have hn2 : ¬(q.2 = j) := fun e => hpq (hp.trans e.symm)
        exact if_neg (fun hcon => hn2 hcon.2)
      · exact if_neg (fun hcon => hp hcon.1)
  rw [hsum]
  by_cases hpq : p.2 = q.2 <;> simp [hpq]

/-- If `⟨ω|ω⟩ = 1`, the product-form matrix satisfies equation (3). -/
theorem productLiouville_exactRestoration {m n : ℕ} (η ω : Fin m → ℂ)
    (hnorm : cinner ω ω = 1) :
    ExactRestoration (productLiouville (n := n) η ω) ω η := by
  classical
  unfold ExactRestoration
  rw [productLiouville_eq]
  ext p j
  simp only [Matrix.mul_apply, kronRankOneId_apply, kronColId_apply]
  have hterm : ∀ i : Fin m, ∀ k : Fin n,
      (η p.1 * star (ω i) * (if p.2 = k then (1 : ℂ) else 0))
        * (ω i * (if k = j then (1 : ℂ) else 0))
      = if p.2 = k ∧ k = j then η p.1 * (star (ω i) * ω i) else 0 := by
    intro i k
    by_cases hp : p.2 = k <;> by_cases hk : k = j <;> simp [hp, hk, mul_assoc]
  conv_lhs =>
    rw [Fintype.sum_prod_type]
    simp only [hterm]
  by_cases hpj : p.2 = j
  · rw [hpj]
    have h2 : ∀ i : Fin m,
        (∑ k : Fin n, if j = k ∧ k = j then η p.1 * (star (ω i) * ω i) else 0)
        = η p.1 * (star (ω i) * ω i) := by
      intro i
      rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hk
        exact if_neg (fun hcon => hk hcon.2)
      · intro hk
        exact absurd (Finset.mem_univ j) hk
    rw [Finset.sum_congr rfl fun i _ => h2 i]
    have hsum : (∑ i : Fin m, η p.1 * (star (ω i) * ω i))
        = η p.1 * ∑ i : Fin m, star (ω i) * ω i :=
      (Finset.mul_sum Finset.univ (fun i => star (ω i) * ω i) (η p.1)).symm
    rw [hsum, ← cinner, hnorm, mul_one]
    simp
  · have hsum : (∑ i : Fin m, ∑ k : Fin n,
        if p.2 = k ∧ k = j then η p.1 * (star (ω i) * ω i) else 0) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hp : p.2 = k
      · have hnj : ¬(k = j) := fun e => hpj (hp.trans e)
        exact if_neg (fun hcon => hnj hcon.2)
      · exact if_neg (fun hcon => hp hcon.1)
    rw [hsum]
    simp [hpj]

/-! ## The acceptance-bias trace identity (4) -/

/-- Factorization `|ω⟩⟨z| ⊗ I = (|ω⟩ ⊗ I)(⟨z| ⊗ I)`. -/
theorem kronRankOneId_eq_mul {m n : ℕ} (ω z : Fin m → ℂ) :
    kronRankOneId (n := n) ω z
      = kronColId (n := n) ω * (kronColId (n := n) z).conjTranspose :=
  (productLiouville_eq ω z).symm

/-- `(⟨z| ⊗ I)(|η⟩ ⊗ I) = ⟨z|η⟩ I_n`. -/
theorem kronColId_conjTranspose_mul {m n : ℕ} (z η : Fin m → ℂ) :
    (kronColId (n := n) z).conjTranspose * kronColId (n := n) η
      = (cinner z η) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  classical
  ext j k
  have hcell : ∀ p : Fin m × Fin n,
      star (kronColId z p j) * kronColId η p k
      = if p.2 = j ∧ p.2 = k then star (z p.1) * η p.1 else 0 := by
    intro p
    by_cases hj : p.2 = j <;> by_cases hk : p.2 = k <;> by_cases hq : k = j <;>
      simp [kronColId_apply, hj, hk, hq, star_mul]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, cinner]
  conv_lhs =>
    rw [Fintype.sum_prod_type]
    simp only [hcell]
  by_cases hjk : j = k
  · rw [hjk]
    have hsum : (∑ i : Fin m, ∑ p : Fin n,
        if p = k ∧ p = k then star (z i) * η i else 0)
        = ∑ i : Fin m, star (z i) * η i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_eq_single k]
      · simp
      · intro p _ hp
        exact if_neg (fun hcon => hp hcon.1)
      · intro hp
        exact absurd (Finset.mem_univ k) hp
    rw [hsum]
    simp
  · have hsum : (∑ i : Fin m, ∑ p : Fin n,
        if p = j ∧ p = k then star (z i) * η i else 0) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      refine Finset.sum_eq_zero fun p _ => ?_
      by_cases hp : p = j
      · have hnk : ¬(p = k) := fun e => hjk (hp.symm.trans e)
        exact if_neg (fun hcon => hnk hcon.2)
      · exact if_neg (fun hcon => hp hcon.1)
    rw [hsum]
    simp [hjk]

/-- **Equation (4).** `Tr[(|ω⟩⟨z| ⊗ I) S] = D² ⟨z|η⟩` under exact restoration. -/
theorem eq4_bias_identity {m n : ℕ}
    {S : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ} {ω η : Fin m → ℂ}
    (h : ExactRestoration S ω η) (z : Fin m → ℂ) :
    Matrix.trace (kronRankOneId ω z * S) = (n : ℂ) * cinner z η := by
  classical
  rw [kronRankOneId_eq_mul]
  have hcycle : Matrix.trace (kronColId (n := n) ω * (kronColId (n := n) z).conjTranspose * S)
      = Matrix.trace (S * kronColId (n := n) ω * (kronColId (n := n) z).conjTranspose) :=
    Matrix.trace_mul_cycle (kronColId (n := n) ω) (kronColId (n := n) z).conjTranspose S
  rw [hcycle]
  have hmid : S * kronColId (n := n) ω * (kronColId (n := n) z).conjTranspose
      = kronColId (n := n) η * (kronColId (n := n) z).conjTranspose := by
    rw [h]
  rw [hmid]
  have hcomm : Matrix.trace (kronColId (n := n) η * (kronColId (n := n) z).conjTranspose)
      = Matrix.trace ((kronColId (n := n) z).conjTranspose * kronColId (n := n) η) :=
    Matrix.trace_mul_comm (kronColId (n := n) η) (kronColId (n := n) z).conjTranspose
  rw [hcomm, kronColId_conjTranspose_mul]
  have hone : Matrix.trace ((cinner z η) • (1 : Matrix (Fin n) (Fin n) ℂ))
      = (cinner z η) * (n : ℂ) := by
    rw [Matrix.trace_smul, Matrix.trace_one]
    show (cinner z η) * (Fintype.card (Fin n) : ℂ) = (cinner z η) * (n : ℂ)
    rw [Fintype.card_fin]
  rw [hone]
  ring

/-- Normalized form of (4): `(1/D²) Tr[(|ω⟩⟨z| ⊗ I) S] = ⟨z|η⟩`. -/
theorem eq4_bias_identity_normalized {m n : ℕ}
    {S : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ} {ω η : Fin m → ℂ}
    (h : ExactRestoration S ω η) (z : Fin m → ℂ) (hn : (n : ℂ) ≠ 0) :
    (1 / (n : ℂ)) * Matrix.trace (kronRankOneId ω z * S) = cinner z η := by
  rw [eq4_bias_identity h z]
  calc (1 / (n : ℂ)) * ((n : ℂ) * cinner z η)
      = ((1 / (n : ℂ)) * (n : ℂ)) * cinner z η := by ring
    _ = cinner z η := by rw [div_mul_cancel₀ _ hn, one_mul]

/-! ## Coefficient comparison and the product-form channel -/

/-- Every square matrix is the linear combination of its matrix units. -/
lemma sum_smul_basisMat {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) :
    (∑ i : Fin d, ∑ j : Fin d, X i j • basisMat i j) = X := by
  classical
  have h : (∑ i : Fin d, ∑ j : Fin d, X i j • basisMat i j)
      = ∑ p : Fin d × Fin d, X p.1 p.2 • basisMat p.1 p.2 :=
    (Fintype.sum_prod_type (fun p : Fin d × Fin d => X p.1 p.2 • basisMat p.1 p.2)).symm
  rw [h]
  ext a b
  have happly : ((∑ p : Fin d × Fin d, X p.1 p.2 • basisMat p.1 p.2) a) b
      = ∑ p : Fin d × Fin d, (X p.1 p.2 • basisMat p.1 p.2) a b := by
    conv_lhs => rw [Finset.sum_apply a Finset.univ _]
    conv_lhs => rw [Finset.sum_apply b Finset.univ _]
  rw [happly]
  have hcell : ∀ p : Fin d × Fin d, (X p.1 p.2 • basisMat p.1 p.2) a b
      = if a = p.1 ∧ b = p.2 then X a b else 0 := by
    intro p
    show X p.1 p.2 * (if a = p.1 ∧ b = p.2 then 1 else 0)
      = if a = p.1 ∧ b = p.2 then X a b else 0
    by_cases hif : a = p.1 ∧ b = p.2
    · rw [if_pos hif, if_pos hif, mul_one, hif.1, hif.2]
    · rw [if_neg hif, if_neg hif, mul_zero]
  rw [Finset.sum_congr rfl fun p _ => hcell p]
  rw [Finset.sum_eq_single (a, b)]
  · exact if_pos ⟨rfl, rfl⟩
  · intro p _ hp
    exact if_neg (fun hcon => hp (Prod.ext hcon.1.symm hcon.2.symm))
  · intro hp
    exact absurd (Finset.mem_univ (a, b)) hp

/-- **Coefficient comparison.** A linear map sending every `|i⟩⟨j|` to
`η ⊗ |i⟩⟨j|` is the product map `X ↦ η ⊗ X`. -/
theorem lemma_2_product_form {k d : ℕ} (η : Matrix (Fin k) (Fin k) ℂ)
    (Ψ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin k × Fin d) (Fin k × Fin d) ℂ)
    (hbasis : ∀ i j : Fin d, Ψ (basisMat i j) = Matrix.kronecker η (basisMat i j))
    (X : Matrix (Fin d) (Fin d) ℂ) :
    Ψ X = Matrix.kronecker η X := by
  classical
  conv_lhs => rw [← sum_smul_basisMat X]
  rw [map_sum]
  conv_lhs => simp only [map_sum]
  simp only [map_smul, hbasis]
  have h : (∑ i : Fin d, ∑ j : Fin d, X i j • Matrix.kronecker η (basisMat i j))
      = ∑ t : Fin d × Fin d, X t.1 t.2 • Matrix.kronecker η (basisMat t.1 t.2) :=
    (Fintype.sum_prod_type
      (fun t : Fin d × Fin d => X t.1 t.2 • Matrix.kronecker η (basisMat t.1 t.2))).symm
  rw [h]
  ext p q
  rcases p with ⟨pa, pb⟩
  rcases q with ⟨qa, qb⟩
  have happly : ((∑ t : Fin d × Fin d, X t.1 t.2 • Matrix.kronecker η (basisMat t.1 t.2))
      (pa, pb)) (qa, qb)
      = ∑ t : Fin d × Fin d,
        (X t.1 t.2 • Matrix.kronecker η (basisMat t.1 t.2)) (pa, pb) (qa, qb) := by
    conv_lhs => rw [Finset.sum_apply (pa, pb) Finset.univ _]
    conv_lhs => rw [Finset.sum_apply (qa, qb) Finset.univ _]
  rw [happly]
  have hcell : ∀ t : Fin d × Fin d,
      (X t.1 t.2 • Matrix.kronecker η (basisMat t.1 t.2)) (pa, pb) (qa, qb)
      = if pb = t.1 ∧ qb = t.2 then η pa qa * X pb qb else 0 := by
    intro t
    show X t.1 t.2 * (η pa qa * basisMat t.1 t.2 pb qb)
      = if pb = t.1 ∧ qb = t.2 then η pa qa * X pb qb else 0
    show X t.1 t.2 * (η pa qa * (if pb = t.1 ∧ qb = t.2 then 1 else 0))
      = if pb = t.1 ∧ qb = t.2 then η pa qa * X pb qb else 0
    by_cases hif : pb = t.1 ∧ qb = t.2
    · rw [if_pos hif, if_pos hif, hif.1, hif.2]
      ring
    · rw [if_neg hif, if_neg hif]
      ring
  rw [Finset.sum_congr rfl fun t _ => hcell t]
  rw [Finset.sum_eq_single (pb, qb)]
  · exact if_pos ⟨rfl, rfl⟩
  · intro t _ ht
    exact if_neg (fun hcon => ht (Prod.ext hcon.1.symm hcon.2.symm))
  · intro hp
    exact absurd (Finset.mem_univ (pb, qb)) hp

/-- **Lemma 2 (Exact restoration), Liouville form.** -/
theorem lemma_2_exact_restoration {m n : ℕ}
    {S : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ} {ω η : Fin m → ℂ}
    (h : ExactRestoration S ω η) :
    (∀ x : Fin n → ℂ, Matrix.mulVec S (kronVec ω x) = kronVec η x) ∧
    (∀ z : Fin m → ℂ,
      Matrix.trace (kronRankOneId ω z * S) = (n : ℂ) * cinner z η) :=
  ⟨exactRestoration_mulVec h, eq4_bias_identity h⟩

/-- Correlations with an inaccessible reference are preserved by the product
form: the entries of `(η ⊗ X) ⊗ R` and `η ⊗ (X ⊗ R)` agree under the
associativity of the tensor factors. -/
theorem preserves_correlations {k d r : ℕ}
    (η : Matrix (Fin k) (Fin k) ℂ)
    (X : Matrix (Fin d) (Fin d) ℂ)
    (R : Matrix (Fin r) (Fin r) ℂ)
    (a a' : Fin k) (b b' : Fin d) (c c' : Fin r) :
    Matrix.kronecker (Matrix.kronecker η X) R ((a, b), c) ((a', b'), c')
      = Matrix.kronecker η (Matrix.kronecker X R) (a, (b, c)) (a', (b', c')) := by
  show (η a a' * X b b') * R c c' = η a a' * (X b b' * R c c')
  ring

end Paper25
