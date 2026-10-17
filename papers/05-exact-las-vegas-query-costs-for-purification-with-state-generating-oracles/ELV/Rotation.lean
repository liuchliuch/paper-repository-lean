import ELV.Hadamard
import ELV.BoundaryOracle
import ELV.LpHilbert

/-! Genuine plane rotations, used for four legal oracle completions. -/
noncomputable section
namespace ELV.Rotation
open ELV.Stabilize
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def rotate (a b : ℝ) (z : HilbertPair E E) : HilbertPair E E :=
  WithLp.toLp 2 ((a : ℂ) • z.fst - (b : ℂ) • z.snd,
    (b : ℂ) • z.fst + (a : ℂ) • z.snd)

lemma rotate_inner (a b : ℝ) (x y : HilbertPair E E) :
    inner ℂ (rotate a b x) (rotate a b y) =
      ((a^2+b^2 : ℝ) : ℂ) * inner ℂ x y := by
  change inner ℂ ((a : ℂ) • x.fst-(b : ℂ) • x.snd)
      ((a : ℂ) • y.fst-(b : ℂ) • y.snd) +
    inner ℂ ((b : ℂ) • x.fst+(a : ℂ) • x.snd)
      ((b : ℂ) • y.fst+(a : ℂ) • y.snd) =
    ((a^2+b^2 : ℝ) : ℂ) * (inner ℂ x.fst y.fst+inner ℂ x.snd y.snd)
  simp only [inner_sub_left,inner_sub_right,inner_add_left,inner_add_right,
    inner_smul_left,inner_smul_right,Complex.conj_ofReal,
    Complex.ofReal_add,Complex.ofReal_pow]
  ring

lemma rotate_inverse (a b : ℝ) (h : a^2+b^2=1) (x : HilbertPair E E) :
    rotate a (-b) (rotate a b x) = x := by
  have hc : (a : ℂ)^2+(b : ℂ)^2=1 := by exact_mod_cast h
  apply (WithLp.equiv 2 (E × E)).injective
  apply Prod.ext <;> change _ = _
  · change (a : ℂ) • ((a : ℂ) • x.fst - (b : ℂ) • x.snd) -
      ((-b : ℝ) : ℂ) • ((b : ℂ) • x.fst + (a : ℂ) • x.snd) = x.fst
    push_cast
    calc
      _ = ((a : ℂ)^2+(b : ℂ)^2) • x.fst := by module
      _ = _ := by rw [hc,one_smul]
  · change ((-b : ℝ) : ℂ) • ((a : ℂ) • x.fst - (b : ℂ) • x.snd) +
      (a : ℂ) • ((b : ℂ) • x.fst + (a : ℂ) • x.snd) = x.snd
    push_cast
    calc
      _ = ((a : ℂ)^2+(b : ℂ)^2) • x.snd := by module
      _ = _ := by rw [hc,one_smul]

def unitary (a b : ℝ) (h : a^2+b^2=1) : HilbertPair E E ≃ₗᵢ[ℂ] HilbertPair E E where
  toLinearEquiv :=
    { toFun := rotate a b
      invFun := rotate a (-b)
      left_inv := rotate_inverse a b h
      right_inv := by
        intro x
        simpa only [neg_neg] using rotate_inverse a (-b) (by nlinarith) x
      map_add' := by
        intro x y
        apply (WithLp.equiv 2 (E × E)).injective
        apply Prod.ext <;> dsimp [rotate] <;> module
      map_smul' := by
        intro c x
        apply (WithLp.equiv 2 (E × E)).injective
        apply Prod.ext <;> dsimp [rotate] <;> module }
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖rotate a b x‖^2=‖x‖^2
    rw [← @inner_self_eq_norm_sq ℂ,← @inner_self_eq_norm_sq ℂ,rotate_inner,h]
    simp

@[simp] lemma unitary_apply (a b : ℝ) (h) (x : HilbertPair E E) : unitary a b h x = rotate a b x := rfl
@[simp] lemma unitary_symm_apply (a b : ℝ) (h) (x : HilbertPair E E) :
    (unitary a b h).symm x = rotate a (-b) x := rfl

lemma rotate_comp (a b c d : ℝ) (x : HilbertPair E E) :
    rotate a b (rotate c d x) = rotate (a*c-b*d) (b*c+a*d) x := by
  apply (WithLp.equiv 2 (E × E)).injective
  apply Prod.ext <;> dsimp [rotate] <;> push_cast <;> module <;> rfl

lemma rotate_symmetric (a b : ℝ) (x : HilbertPair E E) :
    rotate a b x + rotate a (-b) x = (2*(a : ℂ)) • x := by
  apply (WithLp.equiv 2 (E × E)).injective
  apply Prod.ext
  · change ((a : ℂ) • x.fst-(b : ℂ) • x.snd) +
      ((a : ℂ) • x.fst-((-b : ℝ) : ℂ) • x.snd) = (2*(a : ℂ)) • x.fst
    push_cast
    module
  · change ((b : ℂ) • x.fst+(a : ℂ) • x.snd) +
      (((-b : ℝ) : ℂ) • x.fst+(a : ℂ) • x.snd) = (2*(a : ℂ)) • x.snd
    push_cast
    module

/-- A fixed chart splitting the answer register. -/
def answerChart (n : ℕ) : ELV.Model.Mspace n ≃ₗᵢ[ℂ]
    HilbertPair (EuclideanSpace ℂ (Fin n)) (EuclideanSpace ℂ (Fin n)) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    ((finCongr (by omega : 2*n=n+n)).trans finSumFinEquiv.symm)).trans
    (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin n ⊕ Fin n => ℂ))

end ELV.Rotation
