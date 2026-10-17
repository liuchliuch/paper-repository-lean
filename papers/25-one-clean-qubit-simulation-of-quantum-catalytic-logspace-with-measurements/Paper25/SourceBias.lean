import Paper25.Restoration
import Paper25.CPTP

/-!
The concrete output observable of Section 2. The first work qubit is the
output: its `1` outcome has sign +1 and its `0` outcome sign -1. This sign is
retained in the normalized vector used by the catalytic trace identity.
-/
noncomputable section
open scoped ComplexConjugate
namespace Paper25.SourceBias
open Matrix
variable {α : Type*} [Fintype α] [DecidableEq α]

abbrev Work (α : Type*) := Fin 2 × α

def sign (b : Fin 2) : ℂ := if b = 1 then 1 else -1

def observable : Matrix (Work α) (Work α) ℂ := Matrix.diagonal fun i => sign i.1

def accept (η : Matrix (Work α) (Work α) ℂ) : ℝ := ∑ a : α, (η (1, a) (1, a)).re

def expectation (η : Matrix (Work α) (Work α) ℂ) : ℝ :=
  (Matrix.trace (observable * η)).re

lemma observable_square : (observable : Matrix (Work α) (Work α) ℂ) * observable = 1 := by
  rw [observable, Matrix.diagonal_mul_diagonal]
  have h : (fun i : Work α => sign i.1 * sign i.1) = fun _ => (1 : ℂ) := by
    funext i
    rcases i with ⟨b, a⟩
    fin_cases b <;> norm_num [sign]
  rw [h, Matrix.diagonal_one]

lemma trace_observable (η : Matrix (Work α) (Work α) ℂ) :
    Matrix.trace (observable * η) =
      (∑ a : α, η (1, a) (1, a)) - ∑ a : α, η (0, a) (0, a) := by
  simp only [observable, Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul,
    Fintype.sum_prod_type, Fin.sum_univ_two, sign]
  simp
  ring

lemma trace_work (η : Matrix (Work α) (Work α) ℂ) :
    Matrix.trace η = (∑ a : α, η (0, a) (0, a)) + ∑ a : α, η (1, a) (1, a) := by
  simp only [Matrix.trace, Matrix.diag_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- The actual source acceptance probability gives `e = 2p - 1`. -/
theorem expectation_eq_signedBias (η : Matrix (Work α) (Work α) ℂ)
    (hη : Matrix.trace η = 1) : expectation η = 2 * accept η - 1 := by
  unfold expectation accept
  rw [trace_observable]
  have h := congrArg Complex.re hη
  rw [trace_work] at h
  simp only [Complex.add_re, Complex.sub_re, Complex.re_sum, Complex.one_re] at *
  linarith

lemma trace_observable_real (η : Matrix (Work α) (Work α) ℂ) (hη : η.IsHermitian) :
    Matrix.trace (observable * η) = (expectation η : ℂ) := by
  have hd : ∀ i : Work α, η i i = ((η i i).re : ℂ) := by
    intro i
    exact (hη.coe_re_apply_self i).symm
  have h0 : (∑ a : α, η (0, a) (0, a)) =
      ((∑ a : α, (η (0, a) (0, a)).re : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun a _ => hd (0, a))
  have h1 : (∑ a : α, η (1, a) (1, a)) =
      ((∑ a : α, (η (1, a) (1, a)).re : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun a _ => hd (1, a))
  unfold expectation
  rw [trace_observable, h0, h1]
  simp

/-- Row-major operator coordinates on the doubled work register. -/
def vecOp {ι : Type*} (X : Matrix ι ι ℂ) : ι × ι → ℂ := fun p => X p.1 p.2

def innerOp {ι : Type*} [Fintype ι] (X Y : Matrix ι ι ℂ) : ℂ :=
  ∑ p : ι × ι, star (vecOp X p) * vecOp Y p

lemma innerOp_eq_trace {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : Matrix ι ι ℂ) : innerOp X Y = Matrix.trace (X.conjTranspose * Y) := by
  simp only [innerOp, vecOp, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type]
  exact Finset.sum_comm

lemma observable_hermitian : (observable : Matrix (Work α) (Work α) ℂ).IsHermitian := by
  rw [observable, Matrix.isHermitian_diagonal_iff]
  intro i
  change star (sign i.1) = sign i.1
  by_cases h : i.1 = 1 <;> simp [sign, h]

lemma inner_observable_eq_trace (η : Matrix (Work α) (Work α) ℂ) :
    innerOp observable η = Matrix.trace (observable * η) := by
  rw [innerOp_eq_trace, observable_hermitian.eq]

/-- The paper's normalized signed observable vector `z = vec(O)/√K`. -/
def zVector : Work α × Work α → ℂ :=
  fun p => vecOp observable p / (Real.sqrt (Fintype.card (Work α)) : ℂ)

lemma inner_z_eta (η : Matrix (Work α) (Work α) ℂ) :
    (∑ p, star (zVector p) * vecOp η p) =
      Matrix.trace (observable * η) / (Real.sqrt (Fintype.card (Work α)) : ℂ) := by
  calc
    (∑ p, star (zVector p) * vecOp η p) =
        ∑ p : Work α × Work α,
          (star (vecOp observable p) * vecOp η p) /
            (Real.sqrt (Fintype.card (Work α)) : ℂ) := by
      apply Finset.sum_congr rfl
      intro p _
      simp only [zVector, star_div₀, Complex.star_def, Complex.conj_ofReal]
      ring
    _ = innerOp observable η / (Real.sqrt (Fintype.card (Work α)) : ℂ) :=
      (Finset.sum_div _ _ _).symm
    _ = _ := by rw [inner_observable_eq_trace]

/-- Equation (4)'s scalar value, with the observable sign fixed explicitly. -/
theorem inner_z_eta_bias (η : Matrix (Work α) (Work α) ℂ)
    (hη : η.IsHermitian) (ht : Matrix.trace η = 1) :
    (∑ p, star (zVector p) * vecOp η p) =
      ((2 * accept η - 1 : ℝ) : ℂ) / (Real.sqrt (Fintype.card (Work α)) : ℂ) := by
  rw [inner_z_eta, trace_observable_real η hη, expectation_eq_signedBias η ht]

/-- `z` is normalized because `O†O = I` and `Tr(I) = K`. -/
theorem zVector_normalized [Nonempty α] :
    (∑ p : Work α × Work α, star (zVector p) * zVector p) = 1 := by
  have hdim : (0 : ℝ) < Fintype.card (Work α) := by
    exact_mod_cast Fintype.card_pos
  have hs : Real.sqrt (Fintype.card (Work α)) ≠ 0 := (Real.sqrt_pos.mpr hdim).ne'
  have hsC : (Real.sqrt (Fintype.card (Work α)) : ℂ) ≠ 0 := by exact_mod_cast hs
  have hn : (∑ p : Work α × Work α,
      star (vecOp observable p) * vecOp observable p) = (Fintype.card (Work α) : ℂ) := by
    change innerOp observable observable = _
    rw [innerOp_eq_trace, observable_hermitian.eq, observable_square, Matrix.trace_one]
  have hc : (∑ p : Work α × Work α, star (zVector p) * zVector p) =
      (∑ p : Work α × Work α, star (vecOp observable p) * vecOp observable p) /
        (Real.sqrt (Fintype.card (Work α)) : ℂ) ^ 2 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro p _
    simp only [zVector, star_div₀, Complex.star_def, Complex.conj_ofReal]
    ring
  rw [hc, hn]
  have hsq : (Real.sqrt (Fintype.card (Work α)) : ℂ) ^ 2 = (Fintype.card (Work α) : ℂ) := by
    exact_mod_cast Real.sq_sqrt hdim.le
  rw [hsq]
  exact div_self (by exact_mod_cast (ne_of_gt hdim))

/-- The actual clean work input has one nonzero diagonal entry. -/
def cleanWork {ι : Type*} [DecidableEq ι] (w0 : ι) : Matrix ι ι ℂ :=
  Matrix.diagonal fun i => if i = w0 then 1 else 0

lemma cleanWork_vector_normalized {ι : Type*} [Fintype ι] [DecidableEq ι] (w0 : ι) :
    (∑ p : ι × ι, star (vecOp (cleanWork w0) p) * vecOp (cleanWork w0) p) = 1 := by
  classical
  simp [vecOp, cleanWork, Matrix.diagonal_apply, Fintype.sum_prod_type]

/-- A coordinate identification for the finite-vector history API; no state
preparation is postulated by this change of indices. -/
def flatVector {ι : Type*} [Fintype ι] (v : ι → ℂ) : Fin (Fintype.card ι) → ℂ :=
  fun i => v ((Fintype.equivFin ι).symm i)

lemma cinner_flatVector {ι : Type*} [Fintype ι] (u v : ι → ℂ) :
    cinner (flatVector u) (flatVector v) = ∑ i, star (u i) * v i := by
  classical
  unfold cinner flatVector
  exact (Fintype.equivFin ι).symm.sum_comp (fun i => star (u i) * v i)

lemma flat_z_normalized [Nonempty α] :
    cinner (flatVector (zVector : Work α × Work α → ℂ)) (flatVector zVector) = 1 := by
  rw [cinner_flatVector, zVector_normalized]

lemma flat_omega_normalized {ι : Type*} [Fintype ι] [DecidableEq ι] (w0 : ι) :
    cinner (flatVector (vecOp (cleanWork w0))) (flatVector (vecOp (cleanWork w0))) = 1 := by
  rw [cinner_flatVector, cleanWork_vector_normalized]

lemma cinner_flat_z_eta (η : Matrix (Work α) (Work α) ℂ)
    (hη : η.IsHermitian) (ht : Matrix.trace η = 1) :
    cinner (flatVector zVector) (flatVector (vecOp η)) =
      ((2 * accept η - 1 : ℝ) : ℂ) / (Real.sqrt (Fintype.card (Work α)) : ℂ) := by
  rw [cinner_flatVector, inner_z_eta_bias η hη ht]

/-- Explicit finite enumeration with dimension `(card ι)^2`, matching the
history API without changing vectorization order. -/
def operatorIndex (ι : Type*) [Fintype ι] : Fin ((Fintype.card ι)^2) ≃ ι × ι :=
  (finCongr (by simp [pow_two])).trans (Fintype.equivFin (ι × ι)).symm

def historyZ : Fin ((Fintype.card (Work α))^2) → ℂ :=
  zVector ∘ operatorIndex (Work α)

def historyEta (η : Matrix (Work α) (Work α) ℂ) :
    Fin ((Fintype.card (Work α))^2) → ℂ := vecOp η ∘ operatorIndex (Work α)

def historyOmega (w0 : Work α) : Fin ((Fintype.card (Work α))^2) → ℂ :=
  vecOp (cleanWork w0) ∘ operatorIndex (Work α)

lemma historyZ_normalized [Nonempty α] :
    cinner (historyZ : Fin ((Fintype.card (Work α))^2) → ℂ) historyZ = 1 := by
  unfold cinner historyZ
  simp only [Function.comp_apply]
  rw [(operatorIndex (Work α)).sum_comp (fun p => star (zVector p) * zVector p)]
  exact zVector_normalized

lemma historyOmega_normalized (w0 : Work α) :
    cinner (historyOmega w0) (historyOmega w0) = 1 := by
  unfold cinner historyOmega
  simp only [Function.comp_apply]
  rw [(operatorIndex (Work α)).sum_comp (fun p => star (vecOp (cleanWork w0) p) * vecOp (cleanWork w0) p)]
  exact cleanWork_vector_normalized w0

lemma history_z_eta_bias (η : Matrix (Work α) (Work α) ℂ)
    (hη : η.IsHermitian) (ht : Matrix.trace η = 1) :
    cinner historyZ (historyEta η) =
      ((2 * accept η - 1 : ℝ) : ℂ) / (Real.sqrt (Fintype.card (Work α)) : ℂ) := by
  unfold cinner historyZ historyEta
  simp only [Function.comp_apply]
  rw [(operatorIndex (Work α)).sum_comp (fun p => star (zVector p) * vecOp η p)]
  exact inner_z_eta_bias η hη ht

end Paper25.SourceBias
