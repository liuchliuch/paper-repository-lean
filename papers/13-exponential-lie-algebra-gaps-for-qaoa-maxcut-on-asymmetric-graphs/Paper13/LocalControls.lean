import Paper13.GraphDynamics
noncomputable section
namespace Paper13
open Matrix
attribute [local instance] Classical.propDecidable

def singletTestState : QubitBasis 7 := ![0,0,1,0,0,1,1]

lemma localP_sparse_expansion : localP = (8 : ℂ)⁻¹ •
    (1 - basisOp (swapBasis 0 2) - basisOp (swapBasis 1 6) + basisOp (swapBasis 0 2 ∘ swapBasis 1 6) - basisOp (swapBasis 3 5) +
     basisOp (swapBasis 0 2 ∘ swapBasis 3 5) + basisOp (swapBasis 1 6 ∘ swapBasis 3 5) -
     basisOp ((swapBasis 0 2 ∘ swapBasis 1 6) ∘ swapBasis 3 5)) := by
  have hp : localP = (8 : ℂ)⁻¹ •
      (1 - swapAt 0 2 - swapAt 1 6 + swapAt 0 2*swapAt 1 6 - swapAt 3 5 +
       swapAt 0 2*swapAt 3 5 + swapAt 1 6*swapAt 3 5 - swapAt 0 2*swapAt 1 6*swapAt 3 5) := by
    dsimp [localP,singletProj]
    simp only [smul_mul_smul]
    norm_num
    congr 1
    noncomm_ring
  rw [hp]
  change (8 : ℂ)⁻¹ • (1 - basisOp (swapBasis 0 2) - basisOp (swapBasis 1 6) + basisOp (swapBasis 0 2)*basisOp (swapBasis 1 6) - basisOp (swapBasis 3 5) +
     basisOp (swapBasis 0 2)*basisOp (swapBasis 3 5) + basisOp (swapBasis 1 6)*basisOp (swapBasis 3 5) -
     basisOp (swapBasis 0 2)*basisOp (swapBasis 1 6)*basisOp (swapBasis 3 5)) = _
  simp only [basisOp_mul]

lemma localP_entry (x y : QubitBasis 7) : localP x y=(8 : ℂ)⁻¹ *
    ((if x=y then 1 else 0) - (if x=swapBasis 0 2 y then 1 else 0) - (if x=swapBasis 1 6 y then 1 else 0) +
      (if x=(swapBasis 0 2 ∘ swapBasis 1 6) y then 1 else 0) - (if x=swapBasis 3 5 y then 1 else 0) +
      (if x=(swapBasis 0 2 ∘ swapBasis 3 5) y then 1 else 0) + (if x=(swapBasis 1 6 ∘ swapBasis 3 5) y then 1 else 0) -
      (if x=((swapBasis 0 2 ∘ swapBasis 1 6) ∘ swapBasis 3 5) y then 1 else 0)) := by
  rw [localP_sparse_expansion]
  rfl

lemma mul_Xv_entry {n : ℕ} (A : Op n) (v : Fin n) (x y : QubitBasis n) :
    (A*Xv v) x y=A x (flipBit v y) := by
  rw [Xv_basisOp]
  simp only [Matrix.mul_apply,basisOp]
  rw [Fintype.sum_eq_single (flipBit v y)]
  · simp
  · intro z hz; simp [hz]
lemma Xv_mul_entry {n : ℕ} (A : Op n) (v : Fin n) (x y : QubitBasis n) :
    (Xv v*A) x y=A (flipBit v x) y := by
  rw [Xv_basisOp]
  simp only [Matrix.mul_apply,basisOp]
  have hh (z : QubitBasis n) : x=flipBit v z ↔ z=flipBit v x := by
    constructor <;> intro h
    · rw [h,flipBit_involutive v z]
    · rw [h,flipBit_involutive v x]
  simp only [hh]
  rw [Fintype.sum_eq_single (flipBit v x)]
  · simp
  · intro z hz; simp [hz]

lemma localP_test_diagonal : localP (singletTestState) (singletTestState)=(1/8 : ℂ) := by
  let x : QubitBasis 7 := singletTestState
  have h0 : x ≠ (swapBasis 0 2) x := by decide
  have h1 : x ≠ (swapBasis 1 6) x := by decide
  have h2 : x ≠ (swapBasis 0 2 ∘ swapBasis 1 6) x := by decide
  have h3 : x ≠ (swapBasis 3 5) x := by decide
  have h4 : x ≠ (swapBasis 0 2 ∘ swapBasis 3 5) x := by decide
  have h5 : x ≠ (swapBasis 1 6 ∘ swapBasis 3 5) x := by decide
  have h6 : x ≠ ((swapBasis 0 2 ∘ swapBasis 1 6) ∘ swapBasis 3 5) x := by decide
  simp only [Function.comp_apply] at h0 h1 h2 h3 h4 h5 h6
  change localP x x=_
  rw [localP_entry]
  simp only [Function.comp_apply]
  simp only [if_pos rfl,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6]
  norm_num

lemma localP_flip_diagonal_0 : localP (flipBit (0 : Fin 7) singletTestState) (flipBit (0 : Fin 7) singletTestState)=0 := by
  let x : QubitBasis 7 := flipBit (0 : Fin 7) singletTestState
  have h0 : x = (swapBasis 0 2) x := by decide
  have h1 : x ≠ (swapBasis 1 6) x := by decide
  have h2 : x ≠ (swapBasis 0 2 ∘ swapBasis 1 6) x := by decide
  have h3 : x ≠ (swapBasis 3 5) x := by decide
  have h4 : x ≠ (swapBasis 0 2 ∘ swapBasis 3 5) x := by decide
  have h5 : x ≠ (swapBasis 1 6 ∘ swapBasis 3 5) x := by decide
  have h6 : x ≠ ((swapBasis 0 2 ∘ swapBasis 1 6) ∘ swapBasis 3 5) x := by decide
  simp only [Function.comp_apply] at h0 h1 h2 h3 h4 h5 h6
  change localP x x=_
  rw [localP_entry]
  simp only [Function.comp_apply]
  simp only [if_pos rfl,if_pos h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6]
  norm_num

lemma localP_flip_diagonal_1 : localP (flipBit (1 : Fin 7) singletTestState) (flipBit (1 : Fin 7) singletTestState)=0 := by
  let x : QubitBasis 7 := flipBit (1 : Fin 7) singletTestState
  have h0 : x ≠ (swapBasis 0 2) x := by decide
  have h1 : x = (swapBasis 1 6) x := by decide
  have h2 : x ≠ (swapBasis 0 2 ∘ swapBasis 1 6) x := by decide
  have h3 : x ≠ (swapBasis 3 5) x := by decide
  have h4 : x ≠ (swapBasis 0 2 ∘ swapBasis 3 5) x := by decide
  have h5 : x ≠ (swapBasis 1 6 ∘ swapBasis 3 5) x := by decide
  have h6 : x ≠ ((swapBasis 0 2 ∘ swapBasis 1 6) ∘ swapBasis 3 5) x := by decide
  simp only [Function.comp_apply] at h0 h1 h2 h3 h4 h5 h6
  change localP x x=_
  rw [localP_entry]
  simp only [Function.comp_apply]
  simp only [if_pos rfl,if_neg h0,if_pos h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6]
  norm_num

lemma localP_flip_diagonal_2 : localP (flipBit (2 : Fin 7) singletTestState) (flipBit (2 : Fin 7) singletTestState)=0 := by
  let x : QubitBasis 7 := flipBit (2 : Fin 7) singletTestState
  have h0 : x = (swapBasis 0 2) x := by decide
  have h1 : x ≠ (swapBasis 1 6) x := by decide
  have h2 : x ≠ (swapBasis 0 2 ∘ swapBasis 1 6) x := by decide
  have h3 : x ≠ (swapBasis 3 5) x := by decide
  have h4 : x ≠ (swapBasis 0 2 ∘ swapBasis 3 5) x := by decide
  have h5 : x ≠ (swapBasis 1 6 ∘ swapBasis 3 5) x := by decide
  have h6 : x ≠ ((swapBasis 0 2 ∘ swapBasis 1 6) ∘ swapBasis 3 5) x := by decide
  simp only [Function.comp_apply] at h0 h1 h2 h3 h4 h5 h6
  change localP x x=_
  rw [localP_entry]
  simp only [Function.comp_apply]
  simp only [if_pos rfl,if_pos h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6]
  norm_num

lemma localP_flip_diagonal_3 : localP (flipBit (3 : Fin 7) singletTestState) (flipBit (3 : Fin 7) singletTestState)=0 := by
  let x : QubitBasis 7 := flipBit (3 : Fin 7) singletTestState
  have h0 : x ≠ (swapBasis 0 2) x := by decide
  have h1 : x ≠ (swapBasis 1 6) x := by decide
  have h2 : x ≠ (swapBasis 0 2 ∘ swapBasis 1 6) x := by decide
  have h3 : x = (swapBasis 3 5) x := by decide
  have h4 : x ≠ (swapBasis 0 2 ∘ swapBasis 3 5) x := by decide
  have h5 : x ≠ (swapBasis 1 6 ∘ swapBasis 3 5) x := by decide
  have h6 : x ≠ ((swapBasis 0 2 ∘ swapBasis 1 6) ∘ swapBasis 3 5) x := by decide
  simp only [Function.comp_apply] at h0 h1 h2 h3 h4 h5 h6
  change localP x x=_
  rw [localP_entry]
  simp only [Function.comp_apply]
  simp only [if_pos rfl,if_neg h0,if_neg h1,if_neg h2,if_pos h3,if_neg h4,if_neg h5,if_neg h6]
  norm_num

lemma localP_flip_diagonal_5 : localP (flipBit (5 : Fin 7) singletTestState) (flipBit (5 : Fin 7) singletTestState)=0 := by
  let x : QubitBasis 7 := flipBit (5 : Fin 7) singletTestState
  have h0 : x ≠ (swapBasis 0 2) x := by decide
  have h1 : x ≠ (swapBasis 1 6) x := by decide
  have h2 : x ≠ (swapBasis 0 2 ∘ swapBasis 1 6) x := by decide
  have h3 : x = (swapBasis 3 5) x := by decide
  have h4 : x ≠ (swapBasis 0 2 ∘ swapBasis 3 5) x := by decide
  have h5 : x ≠ (swapBasis 1 6 ∘ swapBasis 3 5) x := by decide
  have h6 : x ≠ ((swapBasis 0 2 ∘ swapBasis 1 6) ∘ swapBasis 3 5) x := by decide
  simp only [Function.comp_apply] at h0 h1 h2 h3 h4 h5 h6
  change localP x x=_
  rw [localP_entry]
  simp only [Function.comp_apply]
  simp only [if_pos rfl,if_neg h0,if_neg h1,if_neg h2,if_pos h3,if_neg h4,if_neg h5,if_neg h6]
  norm_num

lemma localP_flip_diagonal_6 : localP (flipBit (6 : Fin 7) singletTestState) (flipBit (6 : Fin 7) singletTestState)=0 := by
  let x : QubitBasis 7 := flipBit (6 : Fin 7) singletTestState
  have h0 : x ≠ (swapBasis 0 2) x := by decide
  have h1 : x = (swapBasis 1 6) x := by decide
  have h2 : x ≠ (swapBasis 0 2 ∘ swapBasis 1 6) x := by decide
  have h3 : x ≠ (swapBasis 3 5) x := by decide
  have h4 : x ≠ (swapBasis 0 2 ∘ swapBasis 3 5) x := by decide
  have h5 : x ≠ (swapBasis 1 6 ∘ swapBasis 3 5) x := by decide
  have h6 : x ≠ ((swapBasis 0 2 ∘ swapBasis 1 6) ∘ swapBasis 3 5) x := by decide
  simp only [Function.comp_apply] at h0 h1 h2 h3 h4 h5 h6
  change localP x x=_
  rw [localP_entry]
  simp only [Function.comp_apply]
  simp only [if_pos rfl,if_neg h0,if_pos h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6]
  norm_num

/-- Each individual non-port mixer control breaks the local invariant sector. -/
theorem localP_not_comm_X (v : Fin 7) (hv : v≠4) : comm localP (Xv v)≠0 := by
  have hentry : comm localP (Xv v) (flipBit v singletTestState) singletTestState= -(1/8 : ℂ) := by
    simp only [comm,Matrix.sub_apply,mul_Xv_entry,Xv_mul_entry]
    rw [flipBit_involutive v singletTestState,localP_test_diagonal]
    fin_cases v
    · change localP (flipBit (0 : Fin 7) singletTestState) (flipBit (0 : Fin 7) singletTestState)-(1/8 : ℂ)= -(1/8 : ℂ)
      rw [localP_flip_diagonal_0]; norm_num
    · change localP (flipBit (1 : Fin 7) singletTestState) (flipBit (1 : Fin 7) singletTestState)-(1/8 : ℂ)= -(1/8 : ℂ)
      rw [localP_flip_diagonal_1]; norm_num
    · change localP (flipBit (2 : Fin 7) singletTestState) (flipBit (2 : Fin 7) singletTestState)-(1/8 : ℂ)= -(1/8 : ℂ)
      rw [localP_flip_diagonal_2]; norm_num
    · change localP (flipBit (3 : Fin 7) singletTestState) (flipBit (3 : Fin 7) singletTestState)-(1/8 : ℂ)= -(1/8 : ℂ)
      rw [localP_flip_diagonal_3]; norm_num
    · exact False.elim (hv rfl)
    · change localP (flipBit (5 : Fin 7) singletTestState) (flipBit (5 : Fin 7) singletTestState)-(1/8 : ℂ)= -(1/8 : ℂ)
      rw [localP_flip_diagonal_5]; norm_num
    · change localP (flipBit (6 : Fin 7) singletTestState) (flipBit (6 : Fin 7) singletTestState)-(1/8 : ℂ)= -(1/8 : ℂ)
      rw [localP_flip_diagonal_6]; norm_num
  intro hzero
  rw [hzero] at hentry
  norm_num at hentry


lemma localP_swapped_02 : localP (swapBasis 0 2 singletTestState) singletTestState= -(1/8 : ℂ) := by
  let x := swapBasis (0 : Fin 7) 2 singletTestState
  let y := singletTestState
  have h0 : x ≠ (id) y := by decide
  have h1 : x = (swapBasis 0 2) y := by decide
  have h2 : x ≠ (swapBasis 1 6) y := by decide
  have h3 : x ≠ (swapBasis 0 2 ∘ swapBasis 1 6) y := by decide
  have h4 : x ≠ (swapBasis 3 5) y := by decide
  have h5 : x ≠ (swapBasis 0 2 ∘ swapBasis 3 5) y := by decide
  have h6 : x ≠ (swapBasis 1 6 ∘ swapBasis 3 5) y := by decide
  have h7 : x ≠ ((swapBasis 0 2 ∘ swapBasis 1 6) ∘ swapBasis 3 5) y := by decide
  simp only [Function.comp_apply,id_eq] at h0 h1 h2 h3 h4 h5 h6 h7
  change localP x y=_
  rw [localP_entry]
  simp only [Function.comp_apply]
  simp only [if_neg h0,if_pos h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7]
  norm_num

lemma localP_swapped_16 : localP (swapBasis 1 6 singletTestState) singletTestState= -(1/8 : ℂ) := by
  let x := swapBasis (1 : Fin 7) 6 singletTestState
  let y := singletTestState
  have h0 : x ≠ (id) y := by decide
  have h1 : x ≠ (swapBasis 0 2) y := by decide
  have h2 : x = (swapBasis 1 6) y := by decide
  have h3 : x ≠ (swapBasis 0 2 ∘ swapBasis 1 6) y := by decide
  have h4 : x ≠ (swapBasis 3 5) y := by decide
  have h5 : x ≠ (swapBasis 0 2 ∘ swapBasis 3 5) y := by decide
  have h6 : x ≠ (swapBasis 1 6 ∘ swapBasis 3 5) y := by decide
  have h7 : x ≠ ((swapBasis 0 2 ∘ swapBasis 1 6) ∘ swapBasis 3 5) y := by decide
  simp only [Function.comp_apply,id_eq] at h0 h1 h2 h3 h4 h5 h6 h7
  change localP x y=_
  rw [localP_entry]
  simp only [Function.comp_apply]
  simp only [if_neg h0,if_neg h1,if_pos h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7]
  norm_num

lemma localP_swapped_35 : localP (swapBasis 3 5 singletTestState) singletTestState= -(1/8 : ℂ) := by
  let x := swapBasis (3 : Fin 7) 5 singletTestState
  let y := singletTestState
  have h0 : x ≠ (id) y := by decide
  have h1 : x ≠ (swapBasis 0 2) y := by decide
  have h2 : x ≠ (swapBasis 1 6) y := by decide
  have h3 : x ≠ (swapBasis 0 2 ∘ swapBasis 1 6) y := by decide
  have h4 : x = (swapBasis 3 5) y := by decide
  have h5 : x ≠ (swapBasis 0 2 ∘ swapBasis 3 5) y := by decide
  have h6 : x ≠ (swapBasis 1 6 ∘ swapBasis 3 5) y := by decide
  have h7 : x ≠ ((swapBasis 0 2 ∘ swapBasis 1 6) ∘ swapBasis 3 5) y := by decide
  simp only [Function.comp_apply,id_eq] at h0 h1 h2 h3 h4 h5 h6 h7
  change localP x y=_
  rw [localP_entry]
  simp only [Function.comp_apply]
  simp only [if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_pos h4,if_neg h5,if_neg h6,if_neg h7]
  norm_num

lemma comm_localP_ZZ_entry (u v : Fin 7) (x y : QubitBasis 7) :
    comm localP (ZZ u v) x y=localP x y *
      (((if y u=0 then (1 : ℂ) else -1)*(if y v=0 then (1 : ℂ) else -1))-
       ((if x u=0 then (1 : ℂ) else -1)*(if x v=0 then (1 : ℂ) else -1))) := by
  simp only [comm,ZZ,Zv_diagonal,Matrix.diagonal_mul_diagonal,Matrix.mul_diagonal,Matrix.diagonal_mul,Matrix.sub_apply]
  ring

lemma localP_not_comm_ZZ_0_1 : comm localP (ZZ (0 : Fin 7) 1)≠0 := by
  have he : comm localP (ZZ (0 : Fin 7) 1) (swapBasis 0 2 singletTestState) singletTestState=-(1/4 : ℂ) := by
    rw [comm_localP_ZZ_entry,localP_swapped_02]
    have h0 : singletTestState (0 : Fin 7)=0 := by decide
    have h1 : singletTestState (1 : Fin 7)=0 := by decide
    have h2 : swapBasis (0 : Fin 7) 2 singletTestState (0 : Fin 7)=1 := by decide
    have h3 : swapBasis (0 : Fin 7) 2 singletTestState (1 : Fin 7)=0 := by decide
    rw [h0,h1,h2,h3]
    norm_num [show (1 : Fin 2)≠0 by decide]
  intro hz
  rw [hz] at he
  norm_num at he

lemma localP_not_comm_ZZ_1_2 : comm localP (ZZ (1 : Fin 7) 2)≠0 := by
  have he : comm localP (ZZ (1 : Fin 7) 2) (swapBasis 1 6 singletTestState) singletTestState=(1/4 : ℂ) := by
    rw [comm_localP_ZZ_entry,localP_swapped_16]
    have h0 : singletTestState (1 : Fin 7)=0 := by decide
    have h1 : singletTestState (2 : Fin 7)=1 := by decide
    have h2 : swapBasis (1 : Fin 7) 6 singletTestState (1 : Fin 7)=1 := by decide
    have h3 : swapBasis (1 : Fin 7) 6 singletTestState (2 : Fin 7)=1 := by decide
    rw [h0,h1,h2,h3]
    norm_num [show (1 : Fin 2)≠0 by decide]
  intro hz
  rw [hz] at he
  norm_num at he

lemma localP_not_comm_ZZ_2_3 : comm localP (ZZ (2 : Fin 7) 3)≠0 := by
  have he : comm localP (ZZ (2 : Fin 7) 3) (swapBasis 0 2 singletTestState) singletTestState=(1/4 : ℂ) := by
    rw [comm_localP_ZZ_entry,localP_swapped_02]
    have h0 : singletTestState (2 : Fin 7)=1 := by decide
    have h1 : singletTestState (3 : Fin 7)=0 := by decide
    have h2 : swapBasis (0 : Fin 7) 2 singletTestState (2 : Fin 7)=0 := by decide
    have h3 : swapBasis (0 : Fin 7) 2 singletTestState (3 : Fin 7)=0 := by decide
    rw [h0,h1,h2,h3]
    norm_num [show (1 : Fin 2)≠0 by decide]
  intro hz
  rw [hz] at he
  norm_num at he

lemma localP_not_comm_ZZ_3_4 : comm localP (ZZ (3 : Fin 7) 4)≠0 := by
  have he : comm localP (ZZ (3 : Fin 7) 4) (swapBasis 3 5 singletTestState) singletTestState=-(1/4 : ℂ) := by
    rw [comm_localP_ZZ_entry,localP_swapped_35]
    have h0 : singletTestState (3 : Fin 7)=0 := by decide
    have h1 : singletTestState (4 : Fin 7)=0 := by decide
    have h2 : swapBasis (3 : Fin 7) 5 singletTestState (3 : Fin 7)=1 := by decide
    have h3 : swapBasis (3 : Fin 7) 5 singletTestState (4 : Fin 7)=0 := by decide
    rw [h0,h1,h2,h3]
    norm_num [show (1 : Fin 2)≠0 by decide]
  intro hz
  rw [hz] at he
  norm_num at he

lemma localP_not_comm_ZZ_4_5 : comm localP (ZZ (4 : Fin 7) 5)≠0 := by
  have he : comm localP (ZZ (4 : Fin 7) 5) (swapBasis 3 5 singletTestState) singletTestState=(1/4 : ℂ) := by
    rw [comm_localP_ZZ_entry,localP_swapped_35]
    have h0 : singletTestState (4 : Fin 7)=0 := by decide
    have h1 : singletTestState (5 : Fin 7)=1 := by decide
    have h2 : swapBasis (3 : Fin 7) 5 singletTestState (4 : Fin 7)=0 := by decide
    have h3 : swapBasis (3 : Fin 7) 5 singletTestState (5 : Fin 7)=0 := by decide
    rw [h0,h1,h2,h3]
    norm_num [show (1 : Fin 2)≠0 by decide]
  intro hz
  rw [hz] at he
  norm_num at he

lemma localP_not_comm_ZZ_5_6 : comm localP (ZZ (5 : Fin 7) 6)≠0 := by
  have he : comm localP (ZZ (5 : Fin 7) 6) (swapBasis 3 5 singletTestState) singletTestState=-(1/4 : ℂ) := by
    rw [comm_localP_ZZ_entry,localP_swapped_35]
    have h0 : singletTestState (5 : Fin 7)=1 := by decide
    have h1 : singletTestState (6 : Fin 7)=1 := by decide
    have h2 : swapBasis (3 : Fin 7) 5 singletTestState (5 : Fin 7)=0 := by decide
    have h3 : swapBasis (3 : Fin 7) 5 singletTestState (6 : Fin 7)=1 := by decide
    rw [h0,h1,h2,h3]
    norm_num [show (1 : Fin 2)≠0 by decide]
  intro hz
  rw [hz] at he
  norm_num at he

lemma localP_not_comm_ZZ_1_5 : comm localP (ZZ (1 : Fin 7) 5)≠0 := by
  have he : comm localP (ZZ (1 : Fin 7) 5) (swapBasis 1 6 singletTestState) singletTestState=(1/4 : ℂ) := by
    rw [comm_localP_ZZ_entry,localP_swapped_16]
    have h0 : singletTestState (1 : Fin 7)=0 := by decide
    have h1 : singletTestState (5 : Fin 7)=1 := by decide
    have h2 : swapBasis (1 : Fin 7) 6 singletTestState (1 : Fin 7)=1 := by decide
    have h3 : swapBasis (1 : Fin 7) 6 singletTestState (5 : Fin 7)=1 := by decide
    rw [h0,h1,h2,h3]
    norm_num [show (1 : Fin 2)≠0 by decide]
  intro hz
  rw [hz] at he
  norm_num at he

lemma localP_not_comm_ZZ_2_5 : comm localP (ZZ (2 : Fin 7) 5)≠0 := by
  have he : comm localP (ZZ (2 : Fin 7) 5) (swapBasis 0 2 singletTestState) singletTestState=-(1/4 : ℂ) := by
    rw [comm_localP_ZZ_entry,localP_swapped_02]
    have h0 : singletTestState (2 : Fin 7)=1 := by decide
    have h1 : singletTestState (5 : Fin 7)=1 := by decide
    have h2 : swapBasis (0 : Fin 7) 2 singletTestState (2 : Fin 7)=0 := by decide
    have h3 : swapBasis (0 : Fin 7) 2 singletTestState (5 : Fin 7)=1 := by decide
    rw [h0,h1,h2,h3]
    norm_num [show (1 : Fin 2)≠0 by decide]
  intro hz
  rw [hz] at he
  norm_num at he

/-- Every internal edge control breaks the same local projector. -/
theorem localP_not_comm_ZZ (u v : Fin 7) (h : H.Adj u v) : comm localP (ZZ u v)≠0 := by
  fin_cases u <;> fin_cases v
  · change comm localP (ZZ (0 : Fin 7) 0)≠0
    exact False.elim ((by decide : ¬H.Adj (0 : Fin 7) 0) h)
  · change comm localP (ZZ (0 : Fin 7) 1)≠0
    exact localP_not_comm_ZZ_0_1
  · change comm localP (ZZ (0 : Fin 7) 2)≠0
    exact False.elim ((by decide : ¬H.Adj (0 : Fin 7) 2) h)
  · change comm localP (ZZ (0 : Fin 7) 3)≠0
    exact False.elim ((by decide : ¬H.Adj (0 : Fin 7) 3) h)
  · change comm localP (ZZ (0 : Fin 7) 4)≠0
    exact False.elim ((by decide : ¬H.Adj (0 : Fin 7) 4) h)
  · change comm localP (ZZ (0 : Fin 7) 5)≠0
    exact False.elim ((by decide : ¬H.Adj (0 : Fin 7) 5) h)
  · change comm localP (ZZ (0 : Fin 7) 6)≠0
    exact False.elim ((by decide : ¬H.Adj (0 : Fin 7) 6) h)
  · change comm localP (ZZ (1 : Fin 7) 0)≠0
    have he : ZZ (1 : Fin 7) 0=ZZ (0 : Fin 7) 1 := (Zv_commute _ _).eq
    rw [he]
    exact localP_not_comm_ZZ_0_1
  · change comm localP (ZZ (1 : Fin 7) 1)≠0
    exact False.elim ((by decide : ¬H.Adj (1 : Fin 7) 1) h)
  · change comm localP (ZZ (1 : Fin 7) 2)≠0
    exact localP_not_comm_ZZ_1_2
  · change comm localP (ZZ (1 : Fin 7) 3)≠0
    exact False.elim ((by decide : ¬H.Adj (1 : Fin 7) 3) h)
  · change comm localP (ZZ (1 : Fin 7) 4)≠0
    exact False.elim ((by decide : ¬H.Adj (1 : Fin 7) 4) h)
  · change comm localP (ZZ (1 : Fin 7) 5)≠0
    exact localP_not_comm_ZZ_1_5
  · change comm localP (ZZ (1 : Fin 7) 6)≠0
    exact False.elim ((by decide : ¬H.Adj (1 : Fin 7) 6) h)
  · change comm localP (ZZ (2 : Fin 7) 0)≠0
    exact False.elim ((by decide : ¬H.Adj (2 : Fin 7) 0) h)
  · change comm localP (ZZ (2 : Fin 7) 1)≠0
    have he : ZZ (2 : Fin 7) 1=ZZ (1 : Fin 7) 2 := (Zv_commute _ _).eq
    rw [he]
    exact localP_not_comm_ZZ_1_2
  · change comm localP (ZZ (2 : Fin 7) 2)≠0
    exact False.elim ((by decide : ¬H.Adj (2 : Fin 7) 2) h)
  · change comm localP (ZZ (2 : Fin 7) 3)≠0
    exact localP_not_comm_ZZ_2_3
  · change comm localP (ZZ (2 : Fin 7) 4)≠0
    exact False.elim ((by decide : ¬H.Adj (2 : Fin 7) 4) h)
  · change comm localP (ZZ (2 : Fin 7) 5)≠0
    exact localP_not_comm_ZZ_2_5
  · change comm localP (ZZ (2 : Fin 7) 6)≠0
    exact False.elim ((by decide : ¬H.Adj (2 : Fin 7) 6) h)
  · change comm localP (ZZ (3 : Fin 7) 0)≠0
    exact False.elim ((by decide : ¬H.Adj (3 : Fin 7) 0) h)
  · change comm localP (ZZ (3 : Fin 7) 1)≠0
    exact False.elim ((by decide : ¬H.Adj (3 : Fin 7) 1) h)
  · change comm localP (ZZ (3 : Fin 7) 2)≠0
    have he : ZZ (3 : Fin 7) 2=ZZ (2 : Fin 7) 3 := (Zv_commute _ _).eq
    rw [he]
    exact localP_not_comm_ZZ_2_3
  · change comm localP (ZZ (3 : Fin 7) 3)≠0
    exact False.elim ((by decide : ¬H.Adj (3 : Fin 7) 3) h)
  · change comm localP (ZZ (3 : Fin 7) 4)≠0
    exact localP_not_comm_ZZ_3_4
  · change comm localP (ZZ (3 : Fin 7) 5)≠0
    exact False.elim ((by decide : ¬H.Adj (3 : Fin 7) 5) h)
  · change comm localP (ZZ (3 : Fin 7) 6)≠0
    exact False.elim ((by decide : ¬H.Adj (3 : Fin 7) 6) h)
  · change comm localP (ZZ (4 : Fin 7) 0)≠0
    exact False.elim ((by decide : ¬H.Adj (4 : Fin 7) 0) h)
  · change comm localP (ZZ (4 : Fin 7) 1)≠0
    exact False.elim ((by decide : ¬H.Adj (4 : Fin 7) 1) h)
  · change comm localP (ZZ (4 : Fin 7) 2)≠0
    exact False.elim ((by decide : ¬H.Adj (4 : Fin 7) 2) h)
  · change comm localP (ZZ (4 : Fin 7) 3)≠0
    have he : ZZ (4 : Fin 7) 3=ZZ (3 : Fin 7) 4 := (Zv_commute _ _).eq
    rw [he]
    exact localP_not_comm_ZZ_3_4
  · change comm localP (ZZ (4 : Fin 7) 4)≠0
    exact False.elim ((by decide : ¬H.Adj (4 : Fin 7) 4) h)
  · change comm localP (ZZ (4 : Fin 7) 5)≠0
    exact localP_not_comm_ZZ_4_5
  · change comm localP (ZZ (4 : Fin 7) 6)≠0
    exact False.elim ((by decide : ¬H.Adj (4 : Fin 7) 6) h)
  · change comm localP (ZZ (5 : Fin 7) 0)≠0
    exact False.elim ((by decide : ¬H.Adj (5 : Fin 7) 0) h)
  · change comm localP (ZZ (5 : Fin 7) 1)≠0
    have he : ZZ (5 : Fin 7) 1=ZZ (1 : Fin 7) 5 := (Zv_commute _ _).eq
    rw [he]
    exact localP_not_comm_ZZ_1_5
  · change comm localP (ZZ (5 : Fin 7) 2)≠0
    have he : ZZ (5 : Fin 7) 2=ZZ (2 : Fin 7) 5 := (Zv_commute _ _).eq
    rw [he]
    exact localP_not_comm_ZZ_2_5
  · change comm localP (ZZ (5 : Fin 7) 3)≠0
    exact False.elim ((by decide : ¬H.Adj (5 : Fin 7) 3) h)
  · change comm localP (ZZ (5 : Fin 7) 4)≠0
    have he : ZZ (5 : Fin 7) 4=ZZ (4 : Fin 7) 5 := (Zv_commute _ _).eq
    rw [he]
    exact localP_not_comm_ZZ_4_5
  · change comm localP (ZZ (5 : Fin 7) 5)≠0
    exact False.elim ((by decide : ¬H.Adj (5 : Fin 7) 5) h)
  · change comm localP (ZZ (5 : Fin 7) 6)≠0
    exact localP_not_comm_ZZ_5_6
  · change comm localP (ZZ (6 : Fin 7) 0)≠0
    exact False.elim ((by decide : ¬H.Adj (6 : Fin 7) 0) h)
  · change comm localP (ZZ (6 : Fin 7) 1)≠0
    exact False.elim ((by decide : ¬H.Adj (6 : Fin 7) 1) h)
  · change comm localP (ZZ (6 : Fin 7) 2)≠0
    exact False.elim ((by decide : ¬H.Adj (6 : Fin 7) 2) h)
  · change comm localP (ZZ (6 : Fin 7) 3)≠0
    exact False.elim ((by decide : ¬H.Adj (6 : Fin 7) 3) h)
  · change comm localP (ZZ (6 : Fin 7) 4)≠0
    exact False.elim ((by decide : ¬H.Adj (6 : Fin 7) 4) h)
  · change comm localP (ZZ (6 : Fin 7) 5)≠0
    have he : ZZ (6 : Fin 7) 5=ZZ (5 : Fin 7) 6 := (Zv_commute _ _).eq
    rw [he]
    exact localP_not_comm_ZZ_5_6
  · change comm localP (ZZ (6 : Fin 7) 6)≠0
    exact False.elim ((by decide : ¬H.Adj (6 : Fin 7) 6) h)
end Paper13
