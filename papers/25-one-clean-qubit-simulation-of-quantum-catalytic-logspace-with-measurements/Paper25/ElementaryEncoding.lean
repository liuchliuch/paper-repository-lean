import Paper25.SelectorLCU
import Paper25.EffectiveCircuitModel
import Paper25.SourceMeasurement

/-!
# Actual elementary source channels have eight-term encodings

The source primitive determines all eight unitary terms. Identity extension
and honest wire reindexing preserve the exact average. Measurements are
expanded as reset, CNOT and dephasing before this construction is applied.
-/
noncomputable section
open scoped ComplexConjugate
namespace Paper25.ElementaryEncoding
open OperationalModel

variable {ι κ ρ : Type*} [Fintype ι] [DecidableEq ι]

/-- An explicit list of the eight selected unitaries and its exact average. -/
structure EightTerms (S : Matrix ι ι ℂ) where
  terms : Fin 8 → Matrix ι ι ℂ
  terms_unitary : ∀ j, terms j ∈ Matrix.unitaryGroup ι ℂ
  average : (1 / 8 : ℂ) • ∑ j, terms j = (1 / 2 : ℂ) • S

abbrev EightChannelTerms (C : KrausChannel ι) := EightTerms C.liouville

lemma reindex_unitary [Fintype κ] [DecidableEq κ] (e : κ ≃ ι)
    (U : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    U.submatrix e e ∈ Matrix.unitaryGroup κ ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  change (U.submatrix e e).conjTranspose * U.submatrix e e = 1
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
  have h : U.conjTranspose * U = 1 := hU.1
  rw [h, Matrix.submatrix_one_equiv]

namespace EightTerms
variable {S : Matrix ι ι ℂ}

def reindex [Fintype κ] [DecidableEq κ] (A : EightTerms S) (e : κ ≃ ι) :
    EightTerms (S.submatrix e e) where
  terms j := (A.terms j).submatrix e e
  terms_unitary j := reindex_unitary e _ (A.terms_unitary j)
  average := by
    ext i j
    have h := congrArg (fun M : Matrix ι ι ℂ => M (e i) (e j)) A.average
    simpa only [Matrix.smul_apply, Matrix.sum_apply, Matrix.submatrix_apply] using h

def tensorRight [Fintype ρ] [DecidableEq ρ] (A : EightTerms S) :
    EightTerms (Matrix.kronecker S (1 : Matrix ρ ρ ℂ)) where
  terms j := Matrix.kronecker (A.terms j) (1 : Matrix ρ ρ ℂ)
  terms_unitary j := by
    exact Matrix.kronecker_mem_unitary (A.terms_unitary j)
      (Matrix.unitaryGroup ρ ℂ).one_mem
  average := by
    ext ⟨a, r⟩ ⟨b, s⟩
    have h := congrArg (fun M : Matrix ι ι ℂ => M a b) A.average
    simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul] at h
    simp only [Matrix.smul_apply, Matrix.sum_apply, Matrix.kronecker,
      Matrix.kroneckerMap_apply, smul_eq_mul, ← Finset.sum_mul]
    simpa only [mul_assoc] using congrArg (fun z : ℂ => z * (1 : Matrix ρ ρ ℂ) r s) h

def tensorLeft [Fintype ρ] [DecidableEq ρ] (A : EightTerms S) :
    EightTerms (Matrix.kronecker (1 : Matrix ρ ρ ℂ) S) where
  terms j := Matrix.kronecker (1 : Matrix ρ ρ ℂ) (A.terms j)
  terms_unitary j := by
    exact Matrix.kronecker_mem_unitary (Matrix.unitaryGroup ρ ℂ).one_mem
      (A.terms_unitary j)
  average := by
    ext ⟨r, a⟩ ⟨s, b⟩
    have h := congrArg (fun M : Matrix ι ι ℂ => M a b) A.average
    simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul] at h
    simp only [Matrix.smul_apply, Matrix.sum_apply, Matrix.kronecker,
      Matrix.kroneckerMap_apply, smul_eq_mul, ← Finset.mul_sum]
    simpa only [mul_assoc, mul_left_comm] using
      congrArg (fun z : ℂ => (1 : Matrix ρ ρ ℂ) r s * z) h

end EightTerms

/-- Honest basis relabeling commutes with Liouville vectorization. -/
theorem relabel_liouville [Fintype κ] [DecidableEq κ] (e : κ ≃ ι)
    (C : KrausChannel ι) :
    (relabelChannel e C).liouville =
      C.liouville.submatrix (e.prodCongr e) (e.prodCongr e) := by
  ext a b
  rfl

/-- Identity extension on physical registers becomes identity extension on both
operator coordinates, with the explicit vectorization shuffle. -/
theorem extendRight_liouville [Fintype ρ] [DecidableEq ρ] (C : KrausChannel ι) :
    (C.extendRight ρ).liouville =
      (Matrix.kronecker C.liouville (1 : Matrix (ρ × ρ) (ρ × ρ) ℂ)).submatrix
        (reshuffleEquiv (α := ι) (β := ρ) (γ := ι) (δ := ρ))
        (reshuffleEquiv (α := ι) (β := ρ) (γ := ι) (δ := ρ)) := by
  ext ⟨⟨a, r⟩, b, s⟩ ⟨⟨i, u⟩, j, v⟩
  by_cases hru : r = u <;> by_cases hsv : s = v <;>
    simp [KrausChannel.liouville, KrausChannel.extendRight, Matrix.submatrix_apply,
      reshuffleEquiv, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
      hru, hsv, Prod.ext_iff, apply_ite]

theorem extendLeft_liouville [Fintype ρ] [DecidableEq ρ] (C : KrausChannel ι) :
    (C.extendLeft ρ).liouville =
      (Matrix.kronecker (1 : Matrix (ρ × ρ) (ρ × ρ) ℂ) C.liouville).submatrix
        (reshuffleEquiv (α := ρ) (β := ι) (γ := ρ) (δ := ι))
        (reshuffleEquiv (α := ρ) (β := ι) (γ := ρ) (δ := ι)) := by
  ext ⟨⟨r, a⟩, s, b⟩ ⟨⟨u, i⟩, v, j⟩
  by_cases hru : r = u <;> by_cases hsv : s = v <;>
    simp [KrausChannel.liouville, KrausChannel.extendLeft, Matrix.submatrix_apply,
      reshuffleEquiv, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
      hru, hsv, Prod.ext_iff, apply_ite]

namespace EightChannelTerms

def relabel [Fintype κ] [DecidableEq κ] {C : KrausChannel ι}
    (A : EightChannelTerms C) (e : κ ≃ ι) : EightChannelTerms (relabelChannel e C) := by
  rw [EightChannelTerms, relabel_liouville]
  exact A.reindex (e.prodCongr e)

def extendRight [Fintype ρ] [DecidableEq ρ] {C : KrausChannel ι}
    (A : EightChannelTerms C) : EightChannelTerms (C.extendRight ρ) := by
  rw [EightChannelTerms, extendRight_liouville]
  exact (A.tensorRight (ρ := ρ × ρ)).reindex reshuffleEquiv

def extendLeft [Fintype ρ] [DecidableEq ρ] {C : KrausChannel ι}
    (A : EightChannelTerms C) : EightChannelTerms (C.extendLeft ρ) := by
  rw [EightChannelTerms, extendLeft_liouville]
  exact (A.tensorLeft (ρ := ρ × ρ)).reindex reshuffleEquiv

def placement {q k : ℕ} (p : Placement q k) {C : KrausChannel (Basis k)}
    (A : EightChannelTerms C) : EightChannelTerms (p.liftChannel C) :=
  (A.extendRight (ρ := Basis (q - k))).relabel p.split

end EightChannelTerms

lemma conjugate_unitary (U : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    U.map conj ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext a b
  have h := congrArg (fun M : Matrix ι ι ℂ => conj (M a b)) hU.1
  simpa [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    Matrix.map_apply, map_sum, Complex.star_def, Matrix.one_apply, apply_ite] using h

lemma unitary_liouville (U : Matrix ι ι ℂ) (hU : U.conjTranspose * U = 1) :
    (KrausChannel.unitary U hU).liouville = Matrix.kronecker U (U.map conj) := by
  ext a b
  simp [KrausChannel.liouville, KrausChannel.unitary, Matrix.kronecker,
    Matrix.kroneckerMap_apply]

/-- Four copies of the actual unitary Liouville operator and four canceling
identity terms, exactly as prescribed in Section 4.1. -/
def unitaryTerms (U : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    EightChannelTerms (KrausChannel.unitary U hU.1) where
  terms := unitaryPaddingTerms (KrausChannel.unitary U hU.1).liouville
  terms_unitary := by
    intro j
    apply unitaryPaddingTerms_unitary
    rw [unitary_liouville]
    exact Matrix.kronecker_mem_unitary hU (conjugate_unitary U hU)
  average := unitaryPaddingTerms_average _

def dephaseTerms : EightChannelTerms KrausChannel.dephase where
  terms := dephasingTerms
  terms_unitary := dephasingTerms_unitary
  average := by rw [KrausChannel.dephase_liouville]; exact dephasingTerms_average

def resetTermsWitness : EightChannelTerms KrausChannel.reset where
  terms := resetTerms
  terms_unitary := resetTerms_unitary
  average := by rw [KrausChannel.reset_liouville]; exact resetTerms_average

end Paper25.ElementaryEncoding
