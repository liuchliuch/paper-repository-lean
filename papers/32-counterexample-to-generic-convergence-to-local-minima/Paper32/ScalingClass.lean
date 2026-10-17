import Paper32.FunctionClass
import Paper32.Extensions

/-! Positive scaling preserves the source's actual function classes.
Polynomial graph formulas are transformed by explicit polynomial substitution.
-/

namespace Paper32
open Set

noncomputable def AffineForm.scale (C : ℝ) (a : AffineForm) : AffineForm :=
  ⟨C * a.x, C * a.y, C * a.c⟩

@[simp] theorem AffineForm.eval_scale (C : ℝ) (a : AffineForm) (z : Point) :
    (a.scale C).eval z = C * a.eval z := by
  simp only [AffineForm.scale, AffineForm.eval]
  ring

/-- The same polyhedral cells work after multiplying every affine formula. -/
theorem finitePiecewiseAffine_scale {f : Point → ℝ} (hf : FinitePiecewiseAffine f) (C : ℝ) :
    FinitePiecewiseAffine (fun z => C * f z) := by
  obtain ⟨ι,hι,cell,a,hpoly,hcover,hform⟩ := hf
  refine ⟨ι,hι,cell,fun i => (a i).scale C,hpoly,hcover,?_⟩
  intro i z hz
  change C * f z = ((a i).scale C).eval z
  rw [AffineForm.eval_scale, hform i z hz]

theorem continuousPiecewiseAffine_scale {f : Point → ℝ}
    (hf : ContinuousPiecewiseAffine f) (C : ℝ) :
    ContinuousPiecewiseAffine (fun z => C * f z) :=
  ⟨continuous_const.mul hf.1,finitePiecewiseAffine_scale hf.2 C⟩

/-- Syntactic substitution by actual real polynomials. -/
noncomputable def PolynomialFormula.substitute {n m : ℕ}
    (σ : Fin n → MvPolynomial (Fin m) ℝ) : PolynomialFormula n → PolynomialFormula m
  | .nonneg p => .nonneg (MvPolynomial.eval₂Hom MvPolynomial.C σ p)
  | .truth => .truth
  | .compl p => .compl (p.substitute σ)
  | .conj p q => .conj (p.substitute σ) (q.substitute σ)
  | .disj p q => .disj (p.substitute σ) (q.substitute σ)

lemma eval_polynomial_substitution {n m : ℕ} (σ : Fin n → MvPolynomial (Fin m) ℝ)
    (p : MvPolynomial (Fin n) ℝ) (q : Fin m → ℝ) :
    MvPolynomial.eval q (MvPolynomial.eval₂Hom MvPolynomial.C σ p) =
      MvPolynomial.eval (fun i => MvPolynomial.eval q (σ i)) p := by
  rw [MvPolynomial.map_eval₂Hom]
  have he : (MvPolynomial.eval q).comp MvPolynomial.C = RingHom.id ℝ := by
    ext r
    simp
  rw [he]
  rfl

@[simp] theorem PolynomialFormula.holds_substitute {n m : ℕ}
    (σ : Fin n → MvPolynomial (Fin m) ℝ) (p : PolynomialFormula n) (q : Fin m → ℝ) :
    (p.substitute σ).Holds q ↔ p.Holds (fun i => MvPolynomial.eval q (σ i)) := by
  induction p with
  | nonneg p => simp only [substitute,Holds,eval_polynomial_substitution]
  | truth => rfl
  | compl p ih => simp only [substitute,Holds,ih]
  | conj p r ihp ihr => simp only [substitute,Holds,ihp,ihr]
  | disj p r ihp ihr => simp only [substitute,Holds,ihp,ihr]

/-- A nonzero output scaling is a polynomial preimage of the original graph. -/
theorem semialgebraic_scale {f : Point → ℝ} (hf : SemialgebraicFunction f)
    {C : ℝ} (hC : C ≠ 0) : SemialgebraicFunction (fun z => C * f z) := by
  obtain ⟨p,hp⟩ := hf
  let σ : Fin 3 → MvPolynomial (Fin 3) ℝ :=
    fun i => if i = 2 then MvPolynomial.C C⁻¹ * MvPolynomial.X 2 else MvPolynomial.X i
  refine ⟨p.substitute σ,?_⟩
  ext q
  simp only [Set.mem_setOf_eq, PolynomialFormula.holds_substitute]
  let q' : Fin 3 → ℝ := fun i => MvPolynomial.eval q (σ i)
  have hq : p.Holds q' ↔ q' 2 = f (q' 0,q' 1) := by
    have hh := Set.ext_iff.mp hp q'
    exact hh.symm
  change q 2 = C * f (q 0,q 1) ↔ p.Holds q'
  rw [hq]
  simp only [q',σ,show (0 : Fin 3) ≠ 2 by decide,show (1 : Fin 3) ≠ 2 by decide,
    if_false,if_true,MvPolynomial.eval_mul,MvPolynomial.eval_C,MvPolynomial.eval_X]
  constructor
  · intro h
    rw [h]
    simp [← mul_assoc,hC]
  · intro h
    have hh := congrArg (fun t : ℝ => C * t) h
    simpa only [← mul_assoc,mul_inv_cancel₀ hC,one_mul] using hh

/-- Complete class preservation for the concrete `C F` in Corollary 7.1. -/
theorem scaledObjective_function_classes {C : ℝ} (hC : 0 < C) :
    ContinuousPiecewiseAffine (scaledObjective C) ∧
    SemialgebraicFunction (scaledObjective C) ∧
    LipschitzWith (‖C‖₊ * 8) (scaledObjective C) := by
  refine ⟨continuousPiecewiseAffine_scale continuousPiecewiseAffine_F C,
    semialgebraic_scale semialgebraic_F hC.ne',?_⟩
  exact (lipschitzWith_smul C (β := ℝ)).comp lipschitz_F

end Paper32
