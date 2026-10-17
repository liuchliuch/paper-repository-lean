import Paper26.BinomialMoments
import Paper26.TensorCopies
import Paper26.TensorSLD
import Paper26.ContinuousPOVM
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Fintype.Powerset

/-!
# Actual projective-filter tensor sectors

The input state may have arbitrary head/tail coherences. A fixed partition of
the copy sites determines a concrete rectangular sector embedding; an arbitrary
collective effect on the retained sites is tensored with identity on rejected
sites and embedded into the actual full input space. Positivity and its Born
factorization are matrix theorems, not experiment assumptions.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder Kronecker

namespace Paper26.CollectiveFiltering
open QuantumModel

section IndexedCopies
variable {J α : Type*} [Fintype J] [DecidableEq J] [Fintype α] [DecidableEq α]

/-- Ordinary tensor powers on any finite copy-site type. -/
def copies (A : Matrix α α ℂ) : Matrix (J → α) (J → α) ℂ :=
  fun x y => ∏ j, A (x j) (y j)

omit [DecidableEq α] in
theorem copies_mul (A B : Matrix α α ℂ) :
    copies (J := J) (A * B) = copies (J := J) A * copies (J := J) B := by
  ext x y
  simpa only [copies, Matrix.mul_apply, Finset.prod_mul_distrib] using
    (Fintype.prod_sum (fun j : J => fun a : α => A (x j) a * B a (y j)))

omit [DecidableEq J] [Fintype α] [DecidableEq α] in
theorem copies_conjTranspose (A : Matrix α α ℂ) :
    copies (J := J) Aᴴ = (copies (J := J) A)ᴴ := by
  ext x y
  simp [copies, Matrix.conjTranspose_apply]

theorem copies_posSemidef (A : Matrix α α ℂ) (hA : A.PosSemidef) :
    (copies (J := J) A).PosSemidef := by
  obtain ⟨R, hR⟩ := TensorCopies.psd_exists_gram A hA
  rw [← hR, copies_mul, copies_conjTranspose]
  exact Matrix.posSemidef_conjTranspose_mul_self _

omit [DecidableEq α] in
theorem copies_trace (A : Matrix α α ℂ) :
    Matrix.trace (copies (J := J) A) = Matrix.trace A ^ Fintype.card J := by
  simpa only [copies, Matrix.trace, Matrix.diag_apply, Finset.prod_const,
    Finset.card_univ] using
    (Fintype.prod_sum (fun _j : J => fun a : α => A a a)).symm

omit [DecidableEq J] [Fintype α] [DecidableEq α] in
theorem copies_smul (c : ℂ) (A : Matrix α α ℂ) :
    copies (J := J) (c • A) = c ^ Fintype.card J • copies (J := J) A := by
  ext x y
  simp [copies, Finset.prod_mul_distrib]

/-- The indexed tensor density is an actual finite tensor-copy state. -/
def indexedDensity (ρ : Density α) : Density (J → α) where
  matrix := copies ρ.matrix
  positive := copies_posSemidef ρ.matrix ρ.positive
  trace_one := by rw [copies_trace, ρ.trace_one, one_pow]

omit [DecidableEq J] [Fintype α] [DecidableEq α] in
theorem copies_reindex {N : ℕ} (e : J ≃ Fin N) (A : Matrix α α ℂ)
    (x y : Fin N → α) :
    copies (J := J) A (x ∘ e) (y ∘ e) = TensorCopies.matrix A N x y := by
  exact e.prod_comp (fun j : Fin N => A (x j) (y j))

end IndexedCopies

section Selector
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- A rectangular matrix selecting a concrete injection of basis vectors. -/
def selector (f : β → α) : Matrix α β ℂ := fun a b => if a = f b then 1 else 0

omit [Fintype β] [DecidableEq β] in
theorem selector_compress (f : β → α) (A : Matrix α α ℂ) (a b : β) :
    ((selector f)ᴴ * A * selector f) a b = A (f a) (f b) := by
  simp [selector, Matrix.mul_apply, Matrix.conjTranspose_apply]

omit [Fintype β] in
theorem selector_isometry (f : β → α) (hf : Function.Injective f) :
    (selector f)ᴴ * selector f = 1 := by
  ext a b
  simp [selector, Matrix.mul_apply, Matrix.conjTranspose_apply, hf.eq_iff,
    Matrix.one_apply, eq_comm]

end Selector

section Sector
variable {K L α β : Type*} [Fintype K] [Fintype L]
  [Fintype α] [Fintype β] [DecidableEq K] [DecidableEq L]
  [DecidableEq α] [DecidableEq β]

/-- Actual basis embedding of the retained/rejected copy-site sector. -/
def sectorMap (z : (K → α) × (L → β)) : (K ⊕ L) → (α ⊕ β) :=
  Sum.elim (fun k => Sum.inl (z.1 k)) (fun l => Sum.inr (z.2 l))

omit [Fintype K] [Fintype L] [Fintype α] [Fintype β]
  [DecidableEq K] [DecidableEq L] [DecidableEq α] [DecidableEq β] in
theorem sectorMap_injective :
    Function.Injective (sectorMap (K := K) (L := L) (α := α) (β := β)) := by
  intro z t h
  apply Prod.ext
  · funext k
    exact Sum.inl.inj (congrFun h (Sum.inl k))
  · funext l
    exact Sum.inr.inj (congrFun h (Sum.inr l))

def sectorIsometry : Matrix ((K ⊕ L) → (α ⊕ β)) ((K → α) × (L → β)) ℂ :=
  selector sectorMap

theorem sectorIsometry_orthonormal :
    (sectorIsometry (K := K) (L := L) (α := α) (β := β))ᴴ *
      sectorIsometry (K := K) (L := L) (α := α) (β := β) = 1 :=
  selector_isometry sectorMap sectorMap_injective

def headBlock (A : Matrix (α ⊕ β) (α ⊕ β) ℂ) : Matrix α α ℂ :=
  A.submatrix Sum.inl Sum.inl

def tailBlock (A : Matrix (α ⊕ β) (α ⊕ β) ℂ) : Matrix β β ℂ :=
  A.submatrix Sum.inr Sum.inr

/-- Compression removes all cross-block coherence without assuming it absent. -/
theorem sector_compress (A : Matrix (α ⊕ β) (α ⊕ β) ℂ) :
    sectorIsometryᴴ * copies (J := K ⊕ L) A * sectorIsometry =
      (copies (J := K) (headBlock A)) ⊗ₖ (copies (J := L) (tailBlock A)) := by
  ext z t
  change ((selector (sectorMap (K := K) (L := L) (α := α) (β := β)))ᴴ *
    copies (J := K ⊕ L) A *
      selector (sectorMap (K := K) (L := L) (α := α) (β := β))) z t = _
  rw [selector_compress]
  simp [copies, sectorMap, headBlock, tailBlock,
    Fintype.prod_sum_type]

theorem kronecker_posSemidef {η ξ : Type*} [Fintype η] [Fintype ξ]
    [DecidableEq η] [DecidableEq ξ]
    (E : Matrix η η ℂ) (F : Matrix ξ ξ ℂ) (hE : E.PosSemidef) (hF : F.PosSemidef) :
    (E ⊗ₖ F).PosSemidef := by
  obtain ⟨R, hR⟩ := TensorCopies.psd_exists_gram E hE
  obtain ⟨S, hS⟩ := TensorCopies.psd_exists_gram F hF
  rw [← hR, ← hS, Matrix.mul_kronecker_mul, ← Matrix.conjTranspose_kronecker]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- An arbitrary collective retained-site effect, with rejected sites ignored. -/
def sectorEffect (E : Matrix (K → α) (K → α) ℂ) :
    Matrix ((K ⊕ L) → (α ⊕ β)) ((K ⊕ L) → (α ⊕ β)) ℂ :=
  sectorIsometry * (E ⊗ₖ (1 : Matrix (L → β) (L → β) ℂ)) * sectorIsometryᴴ

theorem sectorEffect_posSemidef (E : Matrix (K → α) (K → α) ℂ) (hE : E.PosSemidef) :
    (sectorEffect (L := L) (β := β) E).PosSemidef :=
  (kronecker_posSemidef E 1 hE Matrix.PosSemidef.one).mul_mul_conjTranspose_same _

/-- Exact complex Born trace for an arbitrary retained collective effect. -/
theorem sector_trace (A : Matrix (α ⊕ β) (α ⊕ β) ℂ)
    (E : Matrix (K → α) (K → α) ℂ) :
    Matrix.trace (copies (J := K ⊕ L) A * sectorEffect E) =
      Matrix.trace (copies (J := K) (headBlock A) * E) *
        Matrix.trace (tailBlock A) ^ Fintype.card L := by
  unfold sectorEffect
  have hc := sector_compress (K := K) (L := L) A
  calc
    _ = Matrix.trace ((copies (J := K ⊕ L) A * sectorIsometry *
        (E ⊗ₖ (1 : Matrix (L → β) (L → β) ℂ))) * sectorIsometryᴴ) := by
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace (sectorIsometryᴴ * (copies (J := K ⊕ L) A * sectorIsometry *
        (E ⊗ₖ (1 : Matrix (L → β) (L → β) ℂ)))) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((sectorIsometryᴴ * copies (J := K ⊕ L) A * sectorIsometry) *
        (E ⊗ₖ (1 : Matrix (L → β) (L → β) ℂ))) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [hc, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.trace_kronecker, copies_trace]

def headMass (ρ : Density (α ⊕ β)) : ℝ := (Matrix.trace (headBlock ρ.matrix)).re

omit [DecidableEq α] [DecidableEq β] in
theorem headBlock_posSemidef (ρ : Density (α ⊕ β)) : (headBlock ρ.matrix).PosSemidef :=
  ρ.positive.submatrix Sum.inl

omit [DecidableEq α] [DecidableEq β] in
theorem tailBlock_posSemidef (ρ : Density (α ⊕ β)) : (tailBlock ρ.matrix).PosSemidef :=
  ρ.positive.submatrix Sum.inr

omit [DecidableEq α] [DecidableEq β] in
theorem headMass_nonneg (ρ : Density (α ⊕ β)) : 0 ≤ headMass ρ :=
  (headBlock_posSemidef ρ).trace_nonneg.1

omit [DecidableEq α] [DecidableEq β] in
theorem tail_trace (ρ : Density (α ⊕ β)) :
    Matrix.trace (tailBlock ρ.matrix) = (1 - headMass ρ : ℝ) := by
  have ht : Matrix.trace ρ.matrix =
      Matrix.trace (headBlock ρ.matrix) + Matrix.trace (tailBlock ρ.matrix) := by
    simp [Matrix.trace, headBlock, tailBlock, Fintype.sum_sum_type]
  have hh := (headBlock_posSemidef ρ).trace_nonneg.2
  apply Complex.ext
  · have hre := congrArg Complex.re ht
    rw [ρ.trace_one] at hre
    simp only [Complex.one_re, Complex.add_re] at hre
    simp only [Complex.ofReal_re, headMass]
    linarith
  · simpa only [Complex.ofReal_im] using (tailBlock_posSemidef ρ).trace_nonneg.2.symm

omit [DecidableEq α] [DecidableEq β] in
theorem headMass_le_one (ρ : Density (α ⊕ β)) : headMass ρ ≤ 1 := by
  have h := (tailBlock_posSemidef ρ).trace_nonneg.1
  rw [tail_trace] at h
  simp only [Complex.ofReal_re, Complex.zero_re] at h
  linarith

/-- The actual normalized state of a successfully retained copy. -/
def retainedState (ρ : Density (α ⊕ β)) (hw : 0 < headMass ρ) : Density α :=
  CollectiveSubmatrix.normalizedBlock (headBlock ρ.matrix) (headBlock_posSemidef ρ)
    (headMass ρ) rfl hw

omit [DecidableEq α] [DecidableEq β] in
theorem headBlock_eq_mass_smul (ρ : Density (α ⊕ β)) (hw : 0 < headMass ρ) :
    headBlock ρ.matrix = (headMass ρ : ℂ) • (retainedState ρ hw).matrix := by
  change _ = (headMass ρ : ℂ) • (((headMass ρ)⁻¹ : ℝ) : ℂ) • headBlock ρ.matrix
  rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hw.ne', Complex.ofReal_one, one_smul]

/-- The fixed-sector Born factorization uses genuine density matrices and
holds for every collective retained effect, including zero retained sites. -/
theorem sector_born_factorization (ρ : Density (α ⊕ β)) (hw : 0 < headMass ρ)
    (E : Matrix (K → α) (K → α) ℂ) :
    (Matrix.trace ((indexedDensity (J := K ⊕ L) ρ).matrix * sectorEffect E)).re =
      headMass ρ ^ Fintype.card K * (1 - headMass ρ) ^ Fintype.card L *
        (Matrix.trace ((indexedDensity (J := K) (retainedState ρ hw)).matrix * E)).re := by
  change (Matrix.trace (copies (J := K ⊕ L) ρ.matrix * sectorEffect E)).re = _
  rw [sector_trace, headBlock_eq_mass_smul ρ hw, copies_smul, Matrix.smul_mul,
    Matrix.trace_smul, tail_trace]
  simp only [indexedDensity, smul_eq_mul, ← Complex.ofReal_pow, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
  ring

end Sector

section FixedSubset
variable {N : ℕ} {α β : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

/-- Every fixed subset gives a native partition of all actual input-copy sites. -/
def siteEquiv (S : Finset (Fin N)) :
    {j : Fin N // j ∈ S} ⊕ {j : Fin N // j ∉ S} ≃ Fin N :=
  Equiv.sumCompl (fun j => j ∈ S)

def subsetMap (S : Finset (Fin N))
    (z : ({j : Fin N // j ∈ S} → α) × ({j : Fin N // j ∉ S} → β)) :
    Fin N → (α ⊕ β) := sectorMap z ∘ (siteEquiv S).symm

omit [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] in
theorem subsetMap_injective (S : Finset (Fin N)) :
    Function.Injective (subsetMap (α := α) (β := β) S) := by
  intro z t h
  apply sectorMap_injective
  funext j
  have hj := congrFun h (siteEquiv S j)
  simpa only [subsetMap, Function.comp_apply, Equiv.symm_apply_apply] using hj

def subsetIsometry (S : Finset (Fin N)) :
    Matrix (Fin N → (α ⊕ β))
      (({j : Fin N // j ∈ S} → α) × ({j : Fin N // j ∉ S} → β)) ℂ :=
  selector (subsetMap S)

theorem subsetIsometry_orthonormal (S : Finset (Fin N)) :
    (subsetIsometry (α := α) (β := β) S)ᴴ * subsetIsometry (α := α) (β := β) S = 1 :=
  selector_isometry (subsetMap S) (subsetMap_injective S)

theorem subset_compress (S : Finset (Fin N))
    (A : Matrix (α ⊕ β) (α ⊕ β) ℂ) :
    (subsetIsometry S)ᴴ * TensorCopies.matrix A N * subsetIsometry S =
      copies (J := {j : Fin N // j ∈ S}) (headBlock A) ⊗ₖ
        copies (J := {j : Fin N // j ∉ S}) (tailBlock A) := by
  ext z t
  change ((selector (subsetMap (α := α) (β := β) S))ᴴ * TensorCopies.matrix A N *
    selector (subsetMap (α := α) (β := β) S)) z t = _
  rw [selector_compress]
  rw [← copies_reindex (siteEquiv S) A (subsetMap S z) (subsetMap S t)]
  have hz : subsetMap (α := α) (β := β) S z ∘ siteEquiv S = sectorMap z := by
    funext j
    simp [subsetMap]
  have ht : subsetMap (α := α) (β := β) S t ∘ siteEquiv S = sectorMap t := by
    funext j
    simp [subsetMap]
  rw [hz, ht]
  have hc := congrArg (fun M => M z t)
    (sector_compress (K := {j : Fin N // j ∈ S}) (L := {j : Fin N // j ∉ S}) A)
  simpa only [sectorIsometry, selector_compress] using hc

def subsetEffect (S : Finset (Fin N))
    (E : Matrix ({j : Fin N // j ∈ S} → α) ({j : Fin N // j ∈ S} → α) ℂ) :
    Matrix (Fin N → (α ⊕ β)) (Fin N → (α ⊕ β)) ℂ :=
  subsetIsometry S * (E ⊗ₖ (1 : Matrix ({j : Fin N // j ∉ S} → β)
    ({j : Fin N // j ∉ S} → β) ℂ)) * (subsetIsometry S)ᴴ

theorem subsetEffect_posSemidef (S : Finset (Fin N))
    (E : Matrix ({j : Fin N // j ∈ S} → α) ({j : Fin N // j ∈ S} → α) ℂ)
    (hE : E.PosSemidef) : (subsetEffect (β := β) S E).PosSemidef :=
  (kronecker_posSemidef E 1 hE Matrix.PosSemidef.one).mul_mul_conjTranspose_same _

theorem subset_trace (S : Finset (Fin N)) (A : Matrix (α ⊕ β) (α ⊕ β) ℂ)
    (E : Matrix ({j : Fin N // j ∈ S} → α) ({j : Fin N // j ∈ S} → α) ℂ) :
    Matrix.trace (TensorCopies.matrix A N * subsetEffect S E) =
      Matrix.trace (copies (J := {j : Fin N // j ∈ S}) (headBlock A) * E) *
        Matrix.trace (tailBlock A) ^ Fintype.card {j : Fin N // j ∉ S} := by
  unfold subsetEffect
  calc
    _ = Matrix.trace ((TensorCopies.matrix A N * subsetIsometry S *
        (E ⊗ₖ (1 : Matrix ({j : Fin N // j ∉ S} → β)
          ({j : Fin N // j ∉ S} → β) ℂ))) * (subsetIsometry S)ᴴ) := by
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((subsetIsometry S)ᴴ * (TensorCopies.matrix A N * subsetIsometry S *
        (E ⊗ₖ (1 : Matrix ({j : Fin N // j ∉ S} → β)
          ({j : Fin N // j ∉ S} → β) ℂ)))) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (((subsetIsometry S)ᴴ * TensorCopies.matrix A N * subsetIsometry S) *
        (E ⊗ₖ (1 : Matrix ({j : Fin N // j ∉ S} → β)
          ({j : Fin N // j ∉ S} → β) ℂ))) := by simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [subset_compress, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
        Matrix.trace_kronecker, copies_trace]

/-- Actual N-copy Born law for an arbitrary collective retained-state effect
after any fixed subset of projective-filter outcomes. -/
theorem subset_born_factorization (S : Finset (Fin N)) (ρ : Density (α ⊕ β))
    (hw : 0 < headMass ρ)
    (E : Matrix ({j : Fin N // j ∈ S} → α) ({j : Fin N // j ∈ S} → α) ℂ) :
    (Matrix.trace ((TensorCopies.density ρ N).matrix * subsetEffect S E)).re =
      headMass ρ ^ S.card * (1 - headMass ρ) ^ (N - S.card) *
        (Matrix.trace ((indexedDensity (J := {j : Fin N // j ∈ S})
          (retainedState ρ hw)).matrix * E)).re := by
  have hc : Fintype.card {j : Fin N // j ∈ S} = S.card := Fintype.card_coe S
  have ht : Fintype.card {j : Fin N // j ∉ S} = N - S.card := by
    simpa only [Finset.mem_compl, Fintype.card_coe, Finset.card_compl,
      Fintype.card_fin] using (Fintype.card_coe Sᶜ)
  change (Matrix.trace (TensorCopies.matrix ρ.matrix N * subsetEffect S E)).re = _
  rw [subset_trace, headBlock_eq_mass_smul ρ hw, copies_smul, Matrix.smul_mul,
    Matrix.trace_smul, tail_trace, hc, ht]
  simp only [indexedDensity, smul_eq_mul, ← Complex.ofReal_pow, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
  ring

end FixedSubset

section Patterns
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- The two actual orthogonal outcomes of the head/tail projective filter. -/
def oneFilter (b : Bool) : Matrix (α ⊕ β) (α ⊕ β) ℂ :=
  Matrix.diagonal fun x => match b, x with
    | true, Sum.inl _ => 1
    | false, Sum.inr _ => 1
    | _, _ => 0

theorem oneFilter_posSemidef (b : Bool) : (oneFilter (α := α) (β := β) b).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro x
  cases b <;> cases x <;> simp

omit [Fintype α] [Fintype β] in
theorem oneFilter_sum :
    (oneFilter true : Matrix (α ⊕ β) (α ⊕ β) ℂ) + oneFilter false = 1 := by
  ext x y
  by_cases h : x = y
  · subst y
    cases x <;> simp [oneFilter]
  · simp [oneFilter, h]

theorem oneFilter_trace (ρ : Density (α ⊕ β)) (b : Bool) :
    Matrix.trace (ρ.matrix * oneFilter b) =
      if b then (headMass ρ : ℂ) else ((1 - headMass ρ : ℝ) : ℂ) := by
  have hh : Matrix.trace (headBlock ρ.matrix) = (headMass ρ : ℂ) := by
    apply Complex.ext
    · rfl
    · exact (headBlock_posSemidef ρ).trace_nonneg.2.symm
  cases b
  · change Matrix.trace (ρ.matrix * oneFilter false) = ((1 - headMass ρ : ℝ) : ℂ)
    rw [← tail_trace ρ]
    simp [oneFilter, Matrix.trace, Matrix.mul_diagonal, tailBlock, Fintype.sum_sum_type]
  · change Matrix.trace (ρ.matrix * oneFilter true) = (headMass ρ : ℂ)
    rw [← hh]
    simp [oneFilter, Matrix.trace, Matrix.mul_diagonal, headBlock, Fintype.sum_sum_type]

/-- The actual full tensor effect of one complete binary filter transcript. -/
def patternEffect {N : ℕ} (p : Fin N → Bool) : Matrix (Fin N → (α ⊕ β))
    (Fin N → (α ⊕ β)) ℂ := TensorSLD.tensor (fun j => oneFilter (p j))

theorem patternEffect_posSemidef {N : ℕ} (p : Fin N → Bool) :
    (patternEffect (α := α) (β := β) p).PosSemidef := by
  choose R hR using fun j : Fin N =>
    TensorCopies.psd_exists_gram (oneFilter (α := α) (β := β) (p j)) (oneFilter_posSemidef (p j))
  have he : patternEffect (α := α) (β := β) p = (TensorSLD.tensor R)ᴴ * TensorSLD.tensor R := by
    change TensorSLD.tensor (fun j : Fin N => oneFilter (p j)) = _
    rw [← TensorSLD.tensor_conjTranspose, ← TensorSLD.tensor_mul]
    congr 1
    funext j
    exact (hR j).symm
  rw [he]
  exact Matrix.posSemidef_conjTranspose_mul_self _

omit [Fintype α] [Fintype β] in
/-- Summing all actual filter sectors is the full tensor-space identity. -/
theorem patternEffect_total (N : ℕ) :
    (∑ p : Fin N → Bool, patternEffect (α := α) (β := β) p) = 1 := by
  ext x y
  have hs : ∀ j : Fin N, (∑ b : Bool, oneFilter b (x j) (y j)) =
      (1 : Matrix (α ⊕ β) (α ⊕ β) ℂ) (x j) (y j) := by
    intro j
    simp only [Fintype.sum_bool]
    simpa only [Matrix.add_apply, add_comm] using
      congrArg (fun A : Matrix (α ⊕ β) (α ⊕ β) ℂ => A (x j) (y j))
        (oneFilter_sum (α := α) (β := β))
  calc
    _ = ∏ j : Fin N, ∑ b : Bool, oneFilter b (x j) (y j) := by
      simpa only [Matrix.sum_apply, patternEffect, TensorSLD.tensor] using
        (Fintype.prod_sum (fun j : Fin N => fun b : Bool => oneFilter b (x j) (y j))).symm
    _ = TensorSLD.tensor (fun _ : Fin N => (1 : Matrix (α ⊕ β) (α ⊕ β) ℂ)) x y := by
      simp only [hs, TensorSLD.tensor]
    _ = _ := congrArg (fun A : Matrix (Fin N → (α ⊕ β)) (Fin N → (α ⊕ β)) ℂ => A x y)
      (TensorSLD.tensor_one N)

/-- Exact complex probability weight of every actual binary filter transcript. -/
theorem pattern_trace (ρ : Density (α ⊕ β)) {N : ℕ} (p : Fin N → Bool) :
    Matrix.trace ((TensorCopies.density ρ N).matrix * patternEffect p) =
      ∏ j : Fin N, if p j then (headMass ρ : ℂ) else ((1 - headMass ρ : ℝ) : ℂ) := by
  change Matrix.trace (TensorSLD.tensor (fun _ : Fin N => ρ.matrix) *
    TensorSLD.tensor (fun j => oneFilter (p j))) = _
  rw [← TensorSLD.tensor_mul, TensorSLD.tensor_trace]
  simp_rw [oneFilter_trace]

/-- Bernoulli weight of any fixed set of retained sites, under actual Born's rule. -/
theorem finset_pattern_born (ρ : Density (α ⊕ β)) {N : ℕ} (S : Finset (Fin N)) :
    (Matrix.trace ((TensorCopies.density ρ N).matrix *
      patternEffect (fun j => decide (j ∈ S)))).re =
        headMass ρ ^ S.card * (1 - headMass ρ) ^ (N - S.card) := by
  rw [pattern_trace]
  simp only [decide_eq_true_eq]
  rw [Finset.prod_ite]
  have hs : Finset.univ.filter (fun j : Fin N => j ∈ S) = S := by ext j; simp
  have ht : Finset.univ.filter (fun j : Fin N => j ∉ S) = Sᶜ := by ext j; simp
  rw [hs, ht]
  simp only [Finset.prod_const, Finset.card_compl, Fintype.card_fin,
    ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- Grouping the real probabilities of all size-M filter sectors gives the
actual native binomial count weight. No binomial law is assumed. -/
theorem retained_count_born_sum (ρ : Density (α ⊕ β)) (N : ℕ) (m : Fin (N + 1)) :
    (∑ S : {S : Finset (Fin N) // S.card = m.val},
      (Matrix.trace ((TensorCopies.density ρ N).matrix *
        patternEffect (fun j => decide (j ∈ S.val)))).re) =
      (CollectiveSubmatrix.binomialLaw N (headMass ρ) (headMass_nonneg ρ)
        (headMass_le_one ρ)).weight m := by
  simp_rw [finset_pattern_born]
  have he : (fun S : {S : Finset (Fin N) // S.card = m.val} =>
      headMass ρ ^ S.val.card * (1 - headMass ρ) ^ (N - S.val.card)) =
      fun _ => headMass ρ ^ m.val * (1 - headMass ρ) ^ (N - m.val) := by
    funext S
    rw [S.property]
  rw [he]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_finset_len, Fintype.card_fin]
  exact (BinomialMoments.binomialLaw_weight N (headMass ρ) (headMass_nonneg ρ)
    (headMass_le_one ρ) m).symm

open MeasureTheory ContinuousPOVM

/-- A real finite-outcome projective filtering POVM on all N input copies. -/
def patternMeasurement (N : ℕ) [MeasurableSpace (Fin N → Bool)]
    [MeasurableSingletonClass (Fin N → Bool)] :
    DominatedPOVM (Fin N → (α ⊕ β)) (Fin N → Bool) where
  reference := Measure.count
  reference_finite := inferInstance
  effect := patternEffect
  entry_measurable _ _ := measurable_of_countable _
  positive_ae := ae_of_all _ patternEffect_posSemidef
  entry_integrable _ _ := Integrable.of_finite
  total x y := by
    rw [integral_count]
    simpa only [Matrix.sum_apply] using
      congrArg (fun A : Matrix (Fin N → (α ⊕ β)) (Fin N → (α ⊕ β)) ℂ => A x y)
        (patternEffect_total N)

/-- Native equivalence between the set and binary encodings of a transcript. -/
def finitePatternEquiv (N : ℕ) : Finset (Fin N) ≃ (Fin N → Bool) where
  toFun S j := decide (j ∈ S)
  invFun p := Finset.univ.filter (fun j => p j = true)
  left_inv S := by ext j; simp
  right_inv p := by
    funext j
    cases h : p j <;> simp [h]

omit [Fintype α] [Fintype β] in
theorem finsetEffect_total (N : ℕ) :
    (∑ S : Finset (Fin N), patternEffect (α := α) (β := β) (finitePatternEquiv N S)) = 1 := by
  calc
    _ = ∑ p : Fin N → Bool, patternEffect (α := α) (β := β) p :=
      Fintype.sum_equiv (finitePatternEquiv N) _ _ (fun _ => rfl)
    _ = _ := patternEffect_total N

/-- The same real N-copy projective filter, with retained-site sets as outcomes. -/
def finsetMeasurement (N : ℕ) [MeasurableSpace (Finset (Fin N))]
    [MeasurableSingletonClass (Finset (Fin N))] :
    DominatedPOVM (Fin N → (α ⊕ β)) (Finset (Fin N)) where
  reference := Measure.count
  reference_finite := inferInstance
  effect S := patternEffect (finitePatternEquiv N S)
  entry_measurable _ _ := measurable_of_countable _
  positive_ae := ae_of_all _ fun S => patternEffect_posSemidef _
  entry_integrable _ _ := Integrable.of_finite
  total x y := by
    rw [integral_count]
    simpa only [Matrix.sum_apply] using
      congrArg (fun A : Matrix (Fin N → (α ⊕ β)) (Fin N → (α ⊕ β)) ℂ => A x y)
        (finsetEffect_total N)

/-- The actual probability of retaining exactly m copies is the native
binomial PMF, obtained by summing all disjoint size-m filter sectors. -/
theorem binomial_count_probability (N : ℕ) [MeasurableSpace (Finset (Fin N))]
    [MeasurableSingletonClass (Finset (Fin N))]
    (ρ : Density (α ⊕ β)) (m : Fin (N + 1)) :
    (finsetMeasurement N).outcomeMeasure (TensorCopies.density ρ N)
      {S | S.card = m.val} =
      (CollectiveSubmatrix.binomialLaw N (headMass ρ) (headMass_nonneg ρ)
        (headMass_le_one ρ)).toPMF m := by
  rw [DominatedPOVM.outcomeMeasure_apply _ _ (Set.to_countable _).measurableSet]
  change (∫⁻ S in {S : Finset (Fin N) | S.card = m.val}, ENNReal.ofReal
    ((Matrix.trace ((TensorCopies.density ρ N).matrix *
      patternEffect (fun j => decide (j ∈ S)))).re) ∂Measure.count) = _
  rw [lintegral_countable _ (Set.to_countable _)]
  simp only [Measure.count_singleton, mul_one, tsum_fintype]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun S _ =>
    trace_mul_effect_nonneg (TensorCopies.density ρ N) (patternEffect_posSemidef _))]
  change ENNReal.ofReal (∑ S : {S : Finset (Fin N) // S.card = m.val},
    (Matrix.trace ((TensorCopies.density ρ N).matrix *
      patternEffect (fun j => decide (j ∈ S.val)))).re) = _
  rw [retained_count_born_sum ρ N m]
  rfl

def retainedCount {N : ℕ} (S : Finset (Fin N)) : Fin (N + 1) :=
  ⟨S.card, Nat.lt_succ_of_le (by simpa using Finset.card_le_univ S)⟩

/-- Equality of the actual retained-count measure with the native binomial
probability measure, not merely equality of formal moments. -/
theorem binomial_count_law (N : ℕ) [MeasurableSpace (Finset (Fin N))]
    [MeasurableSingletonClass (Finset (Fin N))]
    [MeasurableSpace (Fin (N + 1))] [MeasurableSingletonClass (Fin (N + 1))]
    (ρ : Density (α ⊕ β)) :
    ((finsetMeasurement N).outcomeMeasure (TensorCopies.density ρ N)).map retainedCount =
      (CollectiveSubmatrix.binomialLaw N (headMass ρ) (headMass_nonneg ρ)
        (headMass_le_one ρ)).toPMF.toMeasure := by
  apply Measure.ext_of_singleton
  intro m
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton m),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton m)]
  have he : retainedCount ⁻¹' ({m} : Set (Fin (N + 1))) =
      {S : Finset (Fin N) | S.card = m.val} := by
    ext S
    simp [retainedCount, Fin.ext_iff]
  rw [he]
  exact binomial_count_probability N ρ m

end Patterns
end Paper26.CollectiveFiltering
