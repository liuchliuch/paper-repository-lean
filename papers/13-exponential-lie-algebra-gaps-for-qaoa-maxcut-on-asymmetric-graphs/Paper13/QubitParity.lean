import Paper13.LocalProjector
import Paper13.LieDim
noncomputable section
namespace Paper13
open Matrix
open scoped BigOperators

lemma fin2_flip_iff (a b : Fin 2) : a = 1-b ↔ a ≠ b := by fin_cases a <;> fin_cases b <;> decide

lemma Xv_basisOp {n : ℕ} (v : Fin n) : Xv v = basisOp (flipBit v) := by
  ext x y
  change (if (∀ w, w ≠ v → x w = y w) then pauliX (x v) (y v) else 0) =
    (if x = flipBit v y then 1 else 0)
  have he : x = flipBit v y ↔ (∀ w, w ≠ v → x w = y w) ∧ x v ≠ y v := by
    constructor
    · intro h
      subst x
      constructor
      · intro w hw; simp [flipBit,Function.update_of_ne hw]
      · simp only [flipBit,Function.update_self]
        exact (fin2_flip_iff (1-y v) (y v)).mp rfl
    · rintro ⟨ho,hv⟩
      funext w
      by_cases hw : w = v
      · subst w; simp only [flipBit,Function.update_self]; exact (fin2_flip_iff _ _).mpr hv
      · simp only [flipBit,Function.update_of_ne hw]; exact ho w hw
  by_cases ho : ∀ w, w ≠ v → x w = y w
  · rw [if_pos ho]
    by_cases hv : x v = y v
    · rw [pauliX_eq,if_pos hv,if_neg (fun h => (he.mp h).2 hv)]
    · rw [pauliX_eq,if_neg hv,if_pos (he.mpr ⟨ho,hv⟩)]
  · rw [if_neg ho,if_neg (fun h => ho (he.mp h).1)]

lemma flipBit_involutive {n : ℕ} (v : Fin n) : Function.Involutive (flipBit v) := by
  intro x
  funext w
  by_cases hw : w = v
  · subst w; simp [flipBit]
  · simp [flipBit,Function.update_of_ne hw]

lemma bitFlip_basisOp (n : ℕ) : bitFlip n = basisOp flipState := by
  ext x y
  have he : y = flipState x ↔ x = flipState y := by
    constructor <;> intro h <;> rw [h,flipState_involutive]
  simp only [bitFlip,basisOp,he]

lemma flipState_flipBit {n : ℕ} (v : Fin n) (x : QubitBasis n) :
    flipState (flipBit v x) = flipBit v (flipState x) := by
  funext w
  by_cases hw : w = v
  · subst w; simp [flipState,flipBit]
  · simp [flipState,flipBit,Function.update_of_ne hw]

lemma bitFlip_comm_X {n : ℕ} (v : Fin n) : bitFlip n * Xv v = Xv v * bitFlip n := by
  rw [bitFlip_basisOp,Xv_basisOp,basisOp_mul,basisOp_mul]
  congr 1
  funext x
  exact flipState_flipBit v x

lemma bitFlip_comm_mixer (n : ℕ) : bitFlip n * HXFull n = HXFull n * bitFlip n := by
  simp only [HXFull,Finset.mul_sum,Finset.sum_mul,bitFlip_comm_X]

lemma bitFlip_mul_entry {n : ℕ} (A : Op n) (x y : QubitBasis n) :
    (bitFlip n * A) x y = A (flipState x) y := by
  simp only [Matrix.mul_apply,bitFlip]
  rw [Fintype.sum_eq_single (flipState x)]
  · simp
  · intro z hz; simp [hz]

lemma mul_bitFlip_entry {n : ℕ} (A : Op n) (x y : QubitBasis n) :
    (A * bitFlip n) x y = A x (flipState y) := by
  simp only [Matrix.mul_apply,bitFlip]
  rw [Fintype.sum_eq_single (flipState y)]
  · simp [flipState_involutive]
  · intro z hz
    have hn : y ≠ flipState z := by
      intro h
      apply hz
      rw [h,flipState_involutive]
    simp [hn]

lemma flip_zsign (b : Fin 2) :
    (if 1-b = 0 then (1 : ℂ) else -1) = -(if b = 0 then (1 : ℂ) else -1) := by
  fin_cases b <;> norm_num

lemma bitFlip_anticomm_Z {n : ℕ} (v : Fin n) : bitFlip n * Zv v = -(Zv v * bitFlip n) := by
  ext x y
  rw [Matrix.neg_apply,bitFlip_mul_entry,mul_bitFlip_entry,Zv_diagonal]
  simp only [Matrix.neg_apply,Matrix.diagonal_apply]
  have he : flipState x = y ↔ x = flipState y := by
    constructor
    · intro h; rw [← h,flipState_involutive]
    · intro h; rw [h,flipState_involutive]
  by_cases h : x = flipState y
  · rw [if_pos h,if_pos (he.mpr h)]
    exact flip_zsign (x v)
  · rw [if_neg h,if_neg (fun h2 => h (he.mp h2))]
    simp

lemma bitFlip_comm_ZZ {n : ℕ} (u v : Fin n) : bitFlip n * ZZ u v = ZZ u v * bitFlip n := by
  rw [ZZ,← mul_assoc,bitFlip_anticomm_Z,neg_mul,mul_assoc,bitFlip_anticomm_Z]
  simp [mul_assoc]

lemma bitFlip_trace_zero {n : ℕ} (hn : 0 < n) : Matrix.trace (bitFlip n) = 0 := by
  have he : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  simp only [Matrix.trace,Matrix.diag,bitFlip]
  apply Finset.sum_eq_zero
  intro x hx
  exact if_neg (fun h => flipState_ne_self he h.symm)

lemma swapBasis_flipState {n : ℕ} (a b : Fin n) (x : QubitBasis n) :
    swapBasis a b (flipState x) = flipState (swapBasis a b x) := by
  funext w
  simp only [swapBasis_apply,flipState]
  split_ifs <;> rfl

lemma swapAt_comm_bitFlip {n : ℕ} (a b : Fin n) : swapAt a b * bitFlip n = bitFlip n * swapAt a b := by
  change basisOp (swapBasis a b) * bitFlip n = bitFlip n * basisOp (swapBasis a b)
  rw [bitFlip_basisOp,basisOp_mul,basisOp_mul]
  congr 1
  funext x
  exact swapBasis_flipState a b x

lemma singletProj_comm_bitFlip {n : ℕ} (a b : Fin n) :
    singletProj a b * bitFlip n = bitFlip n * singletProj a b := by
  simp only [singletProj,Matrix.smul_mul,Matrix.mul_smul,sub_mul,mul_sub,one_mul,mul_one,swapAt_comm_bitFlip]

lemma localP_comm_bitFlip : localP * bitFlip 7 = bitFlip 7 * localP := by
  exact ((show Commute (singletProj (0 : Fin 7) 2) (bitFlip 7) from singletProj_comm_bitFlip 0 2).mul_left
    (show Commute (singletProj (1 : Fin 7) 6) (bitFlip 7) from singletProj_comm_bitFlip 1 6)).mul_left
    (show Commute (singletProj (3 : Fin 7) 5) (bitFlip 7) from singletProj_comm_bitFlip 3 5)
/-- Commutation with the port Z forces zero matrix entries across its two eigenvalues. -/
lemma commute_Z_entry_zero {n : ℕ} (P : Op n) (v : Fin n)
    (hP : P*Zv v=Zv v*P) (x y : QubitBasis n) (hxy : x v ≠ y v) : P x y = 0 := by
  have h := congrArg (fun M : Op n => M x y) hP
  rw [Zv_diagonal] at h
  simp only [Matrix.mul_diagonal,Matrix.diagonal_mul] at h
  have hz : (if y v = 0 then (1 : ℂ) else -1) - (if x v = 0 then (1 : ℂ) else -1) ≠ 0 := by
    generalize ha : x v = a at *
    generalize hb : y v = b at *
    fin_cases a <;> fin_cases b <;> norm_num at *
  have he : P x y * ((if y v=0 then (1 : ℂ) else -1)-(if x v=0 then (1 : ℂ) else -1)) = 0 := by
    linear_combination h
  exact (mul_eq_zero.mp he).resolve_right hz

/-- A free port makes the restricted global parity trace zero. -/
theorem trace_mul_bitFlip_of_commute_port {n : ℕ} (P : Op n) (v : Fin n)
    (hP : P*Zv v=Zv v*P) : Matrix.trace (P*bitFlip n)=0 := by
  change (∑ x, (P*bitFlip n) x x)=0
  apply Finset.sum_eq_zero
  intro x hx
  rw [mul_bitFlip_entry]
  apply commute_Z_entry_zero P v hP
  change x v ≠ 1-x v
  exact Ne.symm ((fin2_flip_iff (1-x v) (x v)).mp rfl)

lemma localP_parity_trace : Matrix.trace (localP*bitFlip 7)=0 :=
  trace_mul_bitFlip_of_commute_port localP 4 localP_comm_Z4

lemma localQ_comm_bitFlip : (1-localP)*bitFlip 7=bitFlip 7*(1-localP) := by
  simp only [sub_mul,mul_sub,one_mul,mul_one,localP_comm_bitFlip]

lemma localQ_parity_trace : Matrix.trace ((1-localP)*bitFlip 7)=0 := by
  simp only [sub_mul,one_mul,Matrix.trace_sub,bitFlip_trace_zero (by decide : 0 < 7),localP_parity_trace,sub_self]
end Paper13

