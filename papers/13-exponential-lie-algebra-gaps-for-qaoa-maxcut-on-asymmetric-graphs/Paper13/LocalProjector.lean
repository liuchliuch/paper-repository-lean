import Paper13.Singlet
import Paper13.Amplification
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Projection

/-! # The rank-two projector at the coupling port (paper Lemma 3)
Vertices use zero-based indices. All operators are actual complex matrices.
-/
noncomputable section
namespace Paper13
open Matrix
open scoped BigOperators Kronecker

lemma singletProj_collective_X {n : ℕ} (a b : Fin n) :
    collective pauliX a b * singletProj a b = 0 ∧
    singletProj a b * collective pauliX a b = 0 := singletQ_collectiveX a b

lemma singletProj_collective_Z {n : ℕ} (a b : Fin n) :
    collective pauliZ a b * singletProj a b = 0 ∧
    singletProj a b * collective pauliZ a b = 0 := singletQ_collectiveZ a b

lemma singletProj_isOrth {n : ℕ} (a b : Fin n) : IsOrthProj (singletProj a b) :=
  singletQ_isOrth a b

lemma singletProj_comm {n : ℕ} (a b c d : Fin n)
    (hd : a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d) :
    singletProj a b * singletProj c d = singletProj c d * singletProj a b :=
  singletQ_comm_singletQ a b c d hd

/-- The tensor product of singlets on (1,3), (2,7), (4,6), with qubit 5 free. -/
def localP : Op 7 := singletProj 0 2 * singletProj 1 6 * singletProj 3 5

lemma localP_isOrthProj : IsOrthProj localP := by
  apply orthProj_product_op
  · exact orthProj_product_op (singletProj_isOrth 0 2) (singletProj_isOrth 1 6)
      (singletProj_comm 0 2 1 6 (by decide))
  · exact singletProj_isOrth 3 5
  · exact ((show Commute (singletProj (0 : Fin 7) 2) (singletProj 3 5) from
      singletProj_comm 0 2 3 5 (by decide)).mul_left
      (show Commute (singletProj (1 : Fin 7) 6) (singletProj 3 5) from
      singletProj_comm 1 6 3 5 (by decide))).eq

lemma localP_port_factor (A : Op1) :
    localP * embed A (4 : Fin 7) = embed A (4 : Fin 7) * localP := by
  exact ((show Commute (singletProj (0 : Fin 7) 2) (embed A 4) from
    singletQ_comm_embed A 0 2 4 (by decide) (by decide)).mul_left
    (show Commute (singletProj (1 : Fin 7) 6) (embed A 4) from
    singletQ_comm_embed A 1 6 4 (by decide) (by decide))).mul_left
    (show Commute (singletProj (3 : Fin 7) 5) (embed A 4) from
    singletQ_comm_embed A 3 5 4 (by decide) (by decide))

lemma localP_comm_Z4 : localP * Zv (4 : Fin 7) = Zv 4 * localP :=
  localP_port_factor pauliZ

lemma localP_eq_pair2_first :
    localP = singletProj 1 6 * (singletProj 0 2 * singletProj 3 5) := by
  rw [localP, singletProj_comm 0 2 1 6 (by decide), mul_assoc]

lemma localP_eq_pair3_first :
    localP = singletProj 3 5 * (singletProj 0 2 * singletProj 1 6) := by
  exact ((show Commute (singletProj (0 : Fin 7) 2) (singletProj 3 5) from
      singletProj_comm 0 2 3 5 (by decide)).mul_left
      (show Commute (singletProj (1 : Fin 7) 6) (singletProj 3 5) from
      singletProj_comm 1 6 3 5 (by decide))).eq

lemma collective_mul_localP (A : Op1)
    (h : ∀ a b : Fin 7, collective A a b * singletProj a b = 0) :
    collective A 0 2 * localP = 0 ∧ collective A 1 6 * localP = 0 ∧
    collective A 3 5 * localP = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [localP, ← mul_assoc, ← mul_assoc, h, zero_mul, zero_mul]
  · rw [localP_eq_pair2_first, ← mul_assoc, h, zero_mul]
  · rw [localP_eq_pair3_first, ← mul_assoc, h, zero_mul]

lemma localP_comm_collective_total (A : Op1) (hA : Aᴴ = A)
    (h : ∀ a b : Fin 7, collective A a b * singletProj a b = 0) :
    localP * (embed A 0 + embed A 1 + embed A 2 + embed A 3 + embed A 4 + embed A 5 + embed A 6)
      = (embed A 0 + embed A 1 + embed A 2 + embed A 3 + embed A 4 + embed A 5 + embed A 6) * localP := by
  let S : Op 7 := embed A 0 + embed A 1 + embed A 2 + embed A 3 + embed A 4 + embed A 5 + embed A 6
  have hs : S = collective A 0 2 + collective A 1 6 + collective A 3 5 + embed A 4 := by
    dsimp [S, collective]; abel
  have hl : S * localP = embed A 4 * localP := by
    rw [hs, add_mul, add_mul, add_mul]
    obtain ⟨h1, h2, h3⟩ := collective_mul_localP A h
    rw [h1, h2, h3]; simp
  have hsH : Sᴴ = S := by simp [S, embed_conjTranspose A hA]
  have hr := congrArg Matrix.conjTranspose hl
  rw [conjTranspose_mul, conjTranspose_mul, localP_isOrthProj.1, hsH,
    embed_conjTranspose A hA] at hr
  exact hr.trans ((localP_port_factor A).trans hl.symm)

lemma localP_comm_HX :
    localP * (Xv (0 : Fin 7) + Xv 1 + Xv 2 + Xv 3 + Xv 4 + Xv 5 + Xv 6)
      = (Xv (0 : Fin 7) + Xv 1 + Xv 2 + Xv 3 + Xv 4 + Xv 5 + Xv 6) * localP :=
  localP_comm_collective_total pauliX pauliX_conjTranspose (fun a b => (singletQ_collectiveX a b).1)

/-- Cost Hamiltonian of the actual eight-edge gadget. -/
def Hzz_H : Op 7 :=
  ZZ 0 1 + ZZ 1 2 + ZZ 2 3 + ZZ 3 4 + ZZ 4 5 + ZZ 5 6 + ZZ 1 5 + ZZ 2 5

lemma Zv_diagonal {n : ℕ} (v : Fin n) :
    Zv v = Matrix.diagonal (fun x : QubitBasis n => if x v = 0 then (1 : ℂ) else -1) := by
  ext x y
  by_cases hxy : x = y
  · subst y; simp [Zv, embed, Matrix.diagonal, pauliZ_eq]
  · have hbad : ¬ ((∀ w, w ≠ v → x w = y w) ∧ x v = y v) := by
      rintro ⟨h, hv⟩; apply hxy; funext w
      by_cases hw : w = v
      · simpa [hw] using hv
      · exact h w hw
    simp only [Zv, embed, Matrix.diagonal_apply_ne _ hxy, pauliZ_eq]
    by_cases hoff : ∀ w, w ≠ v → x w = y w
    · rw [if_pos hoff, if_pos (fun hv => hbad ⟨hoff, hv⟩)]
    · rw [if_neg hoff]

lemma Zv_commute {n : ℕ} (u v : Fin n) : Commute (Zv u) (Zv v) := by
  rw [Zv_diagonal, Zv_diagonal]
  change Matrix.diagonal _ * Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  exact mul_comm _ _

lemma Hzz_H_factorization :
    Hzz_H = Zv 1 * (Zv 0 + Zv 2) + (Zv 2 + Zv 4) * (Zv 3 + Zv 5) + Zv 5 * (Zv 1 + Zv 6) := by
  dsimp [Hzz_H, ZZ]
  simp only [mul_add, add_mul]
  rw [(Zv_commute (0 : Fin 7) 1).eq, (Zv_commute (3 : Fin 7) 4).eq,
    (Zv_commute (5 : Fin 7) 6).eq, (Zv_commute (1 : Fin 7) 5).eq]
  abel

lemma Hzz_H_mul_localP : Hzz_H * localP = 0 := by
  obtain ⟨h1, h2, h3⟩ := collective_mul_localP pauliZ (fun a b => (singletQ_collectiveZ a b).1)
  rw [Hzz_H_factorization, add_mul, add_mul]
  change Zv 1 * (collective pauliZ 0 2) * localP +
    (Zv 2 + Zv 4) * (collective pauliZ 3 5) * localP +
    Zv 5 * (collective pauliZ 1 6) * localP = 0
  rw [mul_assoc, mul_assoc, mul_assoc, h1, h2, h3]; simp

lemma Hzz_H_isHerm : Hzz_Hᴴ = Hzz_H := by
  have hZZ : ∀ u v : Fin 7, (ZZ u v)ᴴ = ZZ u v := by
    intro u v
    change (embed pauliZ u * embed pauliZ v)ᴴ = _
    rw [conjTranspose_mul, embed_conjTranspose pauliZ pauliZ_conjTranspose,
      embed_conjTranspose pauliZ pauliZ_conjTranspose]
    exact (Zv_commute v u).eq
  simp [Hzz_H, hZZ]

lemma localP_mul_Hzz_H : localP * Hzz_H = 0 := by
  have h := congrArg Matrix.conjTranspose Hzz_H_mul_localP
  simpa only [conjTranspose_mul, show localPᴴ = localP from localP_isOrthProj.1, Hzz_H_isHerm, conjTranspose_zero] using h

/-- Global Z field. -/
def Hz_H : Op 7 := Zv 0 + Zv 1 + Zv 2 + Zv 3 + Zv 4 + Zv 5 + Zv 6

lemma localP_comm_Hz : localP * Hz_H = Hz_H * localP :=
  localP_comm_collective_total pauliZ pauliZ_conjTranspose (fun a b => (singletQ_collectiveZ a b).1)

lemma lemma3_commutator :
    comm localP (Xv (0 : Fin 7) + Xv 1 + Xv 2 + Xv 3 + Xv 4 + Xv 5 + Xv 6) = 0
    ∧ Hzz_H * localP = 0 ∧ localP * Hzz_H = 0 ∧ comm localP Hz_H = 0 := by
  exact ⟨sub_eq_zero.mpr localP_comm_HX, Hzz_H_mul_localP, localP_mul_Hzz_H,
    sub_eq_zero.mpr localP_comm_Hz⟩
def basisOp {n : ℕ} (f : QubitBasis n → QubitBasis n) : Op n :=
  fun x y => if x = f y then 1 else 0

lemma basisOp_mul {n : ℕ} (f g : QubitBasis n → QubitBasis n) :
    basisOp f * basisOp g = basisOp (f ∘ g) := by
  ext x y
  simp only [Matrix.mul_apply, basisOp]
  rw [Fintype.sum_eq_single (g y)]
  · simp
  · intro z hz; simp [hz]

lemma basisOp_trace {n : ℕ} (f : QubitBasis n → QubitBasis n) :
    Matrix.trace (basisOp f) = ((Finset.univ.filter (fun x => x = f x)).card : ℂ) := by
  simp [Matrix.trace, Matrix.diag, basisOp]

lemma localP_trace : Matrix.trace localP = 2 := by
  have s1 : Matrix.trace (swapAt (0 : Fin 7) 2) = 64 := by
    change Matrix.trace (basisOp (swapBasis (0 : Fin 7) 2)) = 64
    simp only [basisOp_mul, basisOp_trace]
    norm_cast
  have s2 : Matrix.trace (swapAt (1 : Fin 7) 6) = 64 := by
    change Matrix.trace (basisOp (swapBasis (1 : Fin 7) 6)) = 64
    simp only [basisOp_mul, basisOp_trace]
    norm_cast
  have s3 : Matrix.trace (swapAt (3 : Fin 7) 5) = 64 := by
    change Matrix.trace (basisOp (swapBasis (3 : Fin 7) 5)) = 64
    simp only [basisOp_mul, basisOp_trace]
    norm_cast
  have s12 : Matrix.trace (swapAt (0 : Fin 7) 2 * swapAt 1 6) = 32 := by
    change Matrix.trace (basisOp (swapBasis (0 : Fin 7) 2) * basisOp (swapBasis 1 6)) = 32
    simp only [basisOp_mul, basisOp_trace]
    norm_cast
  have s13 : Matrix.trace (swapAt (0 : Fin 7) 2 * swapAt 3 5) = 32 := by
    change Matrix.trace (basisOp (swapBasis (0 : Fin 7) 2) * basisOp (swapBasis 3 5)) = 32
    simp only [basisOp_mul, basisOp_trace]
    norm_cast
  have s23 : Matrix.trace (swapAt (1 : Fin 7) 6 * swapAt 3 5) = 32 := by
    change Matrix.trace (basisOp (swapBasis (1 : Fin 7) 6) * basisOp (swapBasis 3 5)) = 32
    simp only [basisOp_mul, basisOp_trace]
    norm_cast
  have s123 : Matrix.trace (swapAt (0 : Fin 7) 2 * swapAt 1 6 * swapAt 3 5) = 16 := by
    change Matrix.trace (basisOp (swapBasis (0 : Fin 7) 2) * basisOp (swapBasis 1 6) * basisOp (swapBasis 3 5)) = 16
    simp only [basisOp_mul, basisOp_trace]
    norm_cast
  have hp : localP = (8 : ℂ)⁻¹ •
      (1 - swapAt 0 2 - swapAt 1 6 + swapAt 0 2 * swapAt 1 6 - swapAt 3 5 +
       swapAt 0 2 * swapAt 3 5 + swapAt 1 6 * swapAt 3 5 - swapAt 0 2 * swapAt 1 6 * swapAt 3 5) := by
    dsimp [localP, singletProj]
    simp only [smul_mul_smul]
    norm_num
    congr 1
    noncomm_ring
  rw [hp]
  simp only [Matrix.trace_smul, Matrix.trace_add, Matrix.trace_sub]
  rw [s1, s2, s3, s12, s13, s23, s123]
  norm_num [Matrix.trace_one, Fintype.card_fun]

/-- An idempotent complex matrix has trace equal to its range dimension. -/
lemma trace_eq_finrank_of_proj {n : ℕ} (P : Op n) (hP : P * P = P) :
    Matrix.trace P = (Module.finrank ℂ (LinearMap.range (Matrix.toLin' P)) : ℂ) := by
  have hi : IsIdempotentElem (Matrix.toLin' P) := by
    change Matrix.toLin' P ∘ₗ Matrix.toLin' P = Matrix.toLin' P
    rw [← Matrix.toLin'_mul, hP]
  simpa only [Matrix.trace_toLin'_eq] using
    (LinearMap.IsIdempotentElem.isProj_range (Matrix.toLin' P) hi).trace

lemma localP_finrank_two : Module.finrank ℂ (LinearMap.range (Matrix.toLin' localP)) = 2 := by
  have h := trace_eq_finrank_of_proj localP localP_isOrthProj.2
  rw [localP_trace] at h
  exact_mod_cast h.symm

lemma localP_rank_two : Module.rank ℂ (LinearMap.range (Matrix.toLin' localP)) = 2 := by
  rw [← Module.finrank_eq_rank, localP_finrank_two]
  rfl

/-- Port coupling to an arbitrary external operator preserves the local sector. -/
lemma localP_comm_Z_port {α : Type*} [Fintype α] [DecidableEq α] (B : Matrix α α ℂ) :
    (localP ⊗ₖ (1 : Matrix α α ℂ)) * (Zv (4 : Fin 7) ⊗ₖ B) =
      (Zv (4 : Fin 7) ⊗ₖ B) * (localP ⊗ₖ (1 : Matrix α α ℂ)) := by
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, one_mul, mul_one, localP_comm_Z4]


/-- SWAP fixes the uniform vector, hence the singlet projector kills |++>. -/
lemma singletProj_uniform {n : ℕ} (a b : Fin n) :
    (singletProj a b).mulVec (fun _ => (1 : ℂ)) = 0 := by
  have hs : (swapAt a b).mulVec (fun _ => (1 : ℂ)) = fun _ => 1 := by
    ext x
    change (∑ y, swapAt a b x y * 1) = 1
    rw [Fintype.sum_eq_single (swapBasis a b x)]
    · simp [swapAt, swapBasis_involutive]
    · intro y hy
      have hn : x ≠ swapBasis a b y := by
        intro h
        apply hy
        rw [h, swapBasis_involutive]
      simp [swapAt, hn]
  simp only [singletProj, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, hs, sub_self, smul_zero]

/-- The normalized standard initial state is a scalar multiple of this vector,
so the local singlet sector has zero initial amplitude. -/
lemma localP_uniform : localP.mulVec (fun _ => (1 : ℂ)) = 0 := by
  simp only [localP, ← Matrix.mulVec_mulVec, singletProj_uniform, Matrix.mulVec_zero]

/-- Lemma 3, including the genuine rank assertion. -/
theorem lemma3 : IsOrthProj localP ∧
    Module.finrank ℂ (LinearMap.range (Matrix.toLin' localP)) = 2 ∧
    comm localP (Xv (0 : Fin 7) + Xv 1 + Xv 2 + Xv 3 + Xv 4 + Xv 5 + Xv 6) = 0 ∧
    Hzz_H * localP = 0 ∧ localP * Hzz_H = 0 ∧ comm localP Hz_H = 0 :=
  ⟨localP_isOrthProj, localP_finrank_two, lemma3_commutator⟩
end Paper13
