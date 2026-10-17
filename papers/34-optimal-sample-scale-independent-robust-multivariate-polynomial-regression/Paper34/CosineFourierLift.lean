import Paper34.CellOscillation
import Paper34.TensorNorming
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# The source multivariate polynomial as an actual finite Fourier polynomial

The bridge in this file has no external mathematical hypotheses. We expand
the actual monomial support of `MvPolynomial`, prove the coordinate frequency
box bound internally by span induction, and extract finitely supported Fourier
coefficients. The resulting object is exactly `TensorNorming.TrigPolynomial`,
so the kernel reproduction, local-supremum and Nikolskii results apply to the
source polynomial itself.
-/

namespace Paper34.CosineFourierLift

noncomputable section

open scoped BigOperators
open Paper34.Kernel Paper34.TensorNorming

/-- A Fourier span with a separate bound in each coordinate. -/
def boxSpace {n : ℕ} (b : Fin n → ℕ) : Submodule ℂ C(TorusN n, ℂ) :=
  Submodule.span ℂ (monomial '' {k : Fin n → ℤ | ∀ i, (k i).natAbs ≤ b i})

theorem monomial_zero {n : ℕ} :
    monomial (fun _ : Fin n => (0 : ℤ)) = (1 : C(TorusN n, ℂ)) := by
  ext x
  simp [monomial]

theorem monomial_add {n : ℕ} (k l : Fin n → ℤ) :
    monomial (k + l) = monomial k * monomial l := by
  ext x
  simp only [monomial, ContinuousMap.coe_mk, Pi.add_apply,
    fourier_add, Finset.prod_mul_distrib, ContinuousMap.mul_apply]

theorem monomial_mem {n : ℕ} (b : Fin n → ℕ) (k : Fin n → ℤ)
    (hk : ∀ i, (k i).natAbs ≤ b i) : monomial k ∈ boxSpace b :=
  Submodule.subset_span ⟨k, hk, rfl⟩

theorem boxSpace_mono {n : ℕ} {b c : Fin n → ℕ} (hbc : ∀ i, b i ≤ c i) :
    boxSpace b ≤ boxSpace c := by
  apply Submodule.span_mono
  rintro _ ⟨k, hk, rfl⟩
  exact ⟨k, fun i => (hk i).trans (hbc i), rfl⟩

theorem one_mem {n : ℕ} (b : Fin n → ℕ) : (1 : C(TorusN n, ℂ)) ∈ boxSpace b := by
  rw [← monomial_zero]
  exact monomial_mem b _ (fun i => by simp)

/-- The frequency-box Minkowski bound for genuine products. -/
theorem mul_mem {n : ℕ} {b c : Fin n → ℕ} {f g : C(TorusN n, ℂ)}
    (hf : f ∈ boxSpace b) (hg : g ∈ boxSpace c) :
    f * g ∈ boxSpace (fun i => b i + c i) := by
  induction hf, hg using Submodule.span_induction₂ with
  | mem_mem u v hu hv =>
      rcases hu with ⟨k, hk, rfl⟩
      rcases hv with ⟨l, hl, rfl⟩
      rw [← monomial_add]
      exact monomial_mem _ _ (fun i =>
        (Int.natAbs_add_le (k i) (l i)).trans (Nat.add_le_add (hk i) (hl i)))
  | zero_left => simp
  | zero_right => simp
  | add_left u v w _ _ _ huw hvw =>
      simpa only [add_mul] using add_mem huw hvw
  | add_right u v w _ _ _ huv huw =>
      simpa only [mul_add] using add_mem huv huw
  | smul_left a u v _ _ huv =>
      simpa only [smul_mul_assoc] using (boxSpace _).smul_mem a huv
  | smul_right a u v _ _ huv =>
      simpa only [mul_smul_comm] using (boxSpace _).smul_mem a huv

theorem prod_mem {n : ℕ} (S : Finset (Fin n))
    (f : Fin n → C(TorusN n, ℂ)) (b : Fin n → Fin n → ℕ)
    (hf : ∀ i ∈ S, f i ∈ boxSpace (b i)) :
    (∏ i ∈ S, f i) ∈ boxSpace (fun j => ∑ i ∈ S, b i j) := by
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty, Finset.sum_empty] using one_mem (fun _ => 0)
  | @insert i S hi ih =>
      have hh := mul_mem (hf i (Finset.mem_insert_self i S))
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
      simpa only [Finset.prod_insert hi, Finset.sum_insert hi] using hh

theorem monomial_single {n : ℕ} (i : Fin n) (k : ℤ) (x : TorusN n) :
    monomial (Pi.single i k) x = fourier k (x i) := by
  change (∏ j : Fin n, fourier ((Pi.single i k : Fin n → ℤ) j) (x j)) = _
  have h : (∏ j : Fin n, fourier ((Pi.single i k : Fin n → ℤ) j) (x j)) =
      fourier ((Pi.single i k : Fin n → ℤ) i) (x i) :=
    Finset.prod_eq_single i
      (fun j _ hji => by rw [Pi.single_eq_of_ne hji, fourier_zero])
      (fun hi => False.elim (hi (Finset.mem_univ i)))
  simpa only [Pi.single_eq_same] using h

/-- The actual continuous cosine coordinate on the common product torus. -/
def cosineCoordinate {n : ℕ} (i : Fin n) : C(TorusN n, ℂ) :=
  (2 : ℂ)⁻¹ • (monomial (Pi.single i 1) + monomial (Pi.single i (-1)))

theorem cosineCoordinate_angular {n : ℕ} (i : Fin n) (theta : Point n) :
    cosineCoordinate i (angularPoint theta) = (Real.cos (theta i) : ℂ) := by
  have h := congrFun TrigBernstein.cos_eq_characters (theta i)
  simpa only [cosineCoordinate, ContinuousMap.smul_apply, ContinuousMap.add_apply,
    monomial_single, angularPoint, TrigBernstein.character, Pi.smul_apply,
    Pi.add_apply, smul_eq_mul] using h.symm

theorem cosineCoordinate_mem {n : ℕ} (i : Fin n) :
    cosineCoordinate i ∈ boxSpace (Pi.single i 1) := by
  apply Submodule.smul_mem
  apply Submodule.add_mem
  · apply monomial_mem
    intro j
    by_cases hji : j = i
    · subst j; simp
    · simp [Pi.single_apply, hji]
  · apply monomial_mem
    intro j
    by_cases hji : j = i
    · subst j; simp
    · simp [Pi.single_apply, hji]

theorem cosineCoordinate_pow_mem {n : ℕ} (i : Fin n) (r : ℕ) :
    cosineCoordinate i ^ r ∈ boxSpace (Pi.single i r) := by
  induction r with
  | zero => simpa only [pow_zero] using one_mem (Pi.single i 0)
  | succ r ih =>
      have h := mul_mem ih (cosineCoordinate_mem i)
      have hb : (fun j => (Pi.single i r : Fin n → ℕ) j + (Pi.single i 1 : Fin n → ℕ) j) =
          Pi.single i (r + 1) := by
        funext j
        by_cases hji : j = i
        · subst j; simp
        · simp [Pi.single_apply, hji]
      rw [hb] at h
      simpa only [pow_succ] using h

theorem product_cosine_powers_mem {n : ℕ} (s : Fin n →₀ ℕ) :
    (∏ i : Fin n, cosineCoordinate i ^ s i) ∈ boxSpace (fun i => s i) := by
  have h := prod_mem Finset.univ (fun i => cosineCoordinate i ^ s i)
    (fun i => Pi.single i (s i)) (fun i _ => cosineCoordinate_pow_mem i (s i))
  have hb : (fun j => ∑ i : Fin n, (Pi.single i (s i) : Fin n → ℕ) j) =
      (fun j => s j) := by
    funext j
    simp [Pi.single_apply]
  rw [hb] at h
  exact h

/-- Expand the actual source polynomial into continuous cosine monomials. -/
def cosinePolynomial {n : ℕ} (q : MvPolynomial (Fin n) ℝ) : C(TorusN n, ℂ) :=
  ∑ s ∈ q.support, Complex.ofReal (q.coeff s) • ∏ i : Fin n, cosineCoordinate i ^ s i

theorem cosinePolynomial_mem {n d : ℕ} (q : PolynomialSpace n d) :
    cosinePolynomial q.1 ∈ boxSpace (fun _ => d) := by
  apply Submodule.sum_mem
  intro s hs
  apply Submodule.smul_mem
  exact boxSpace_mono
    ((MvPolynomial.mem_restrictDegree (Fin n) q.1 d).mp q.2 s hs)
    (product_cosine_powers_mem s)

theorem cosinePolynomial_eval₂ {n : ℕ} (q : MvPolynomial (Fin n) ℝ) (x : TorusN n) :
    cosinePolynomial q x =
      MvPolynomial.eval₂ Complex.ofRealHom (fun i => cosineCoordinate i x) q := by
  simp only [cosinePolynomial, MvPolynomial.eval₂_eq', ContinuousMap.sum_apply,
    ContinuousMap.smul_apply, ContinuousMap.prod_apply, ContinuousMap.pow_apply,
    smul_eq_mul, Complex.ofRealHom_eq_coe]

/-- Finite Fourier coefficients are extracted from proved span membership. -/
theorem exists_fourier_representation {n d : ℕ} (F : C(TorusN n, ℂ))
    (hF : F ∈ boxSpace (fun _ => d)) :
    ∃ H : TrigPolynomial n d, H.toContinuousMap = F := by
  obtain ⟨l, hl, he⟩ := (Finsupp.mem_span_image_iff_linearCombination ℂ).mp hF
  let H : TrigPolynomial n d :=
    { frequencies := l.support
      coeff := l
      degree := fun k hk i => ((Finsupp.mem_supported ℂ l).mp hl hk) i }
  refine ⟨H, ?_⟩
  change (∑ k ∈ l.support, l k • monomial k) = F
  simpa only [Finsupp.linearCombination_apply, Finsupp.sum] using he

/-- A genuine finite Fourier object representing the given source polynomial. -/
def toTrigPolynomial {n d : ℕ} (q : PolynomialSpace n d) : TrigPolynomial n d :=
  Classical.choose (exists_fourier_representation (cosinePolynomial q.1) (cosinePolynomial_mem q))

theorem toTrigPolynomial_spec {n d : ℕ} (q : PolynomialSpace n d) :
    (toTrigPolynomial q).toContinuousMap = cosinePolynomial q.1 :=
  Classical.choose_spec
    (exists_fourier_representation (cosinePolynomial q.1) (cosinePolynomial_mem q))

/-- Full-torus evaluation identity, not only an identity on selected samples. -/
theorem toTrigPolynomial_eval₂ {n d : ℕ} (q : PolynomialSpace n d) (x : TorusN n) :
    (toTrigPolynomial q).eval x =
      MvPolynomial.eval₂ Complex.ofRealHom (fun i => cosineCoordinate i x) q.1 := by
  rw [TrigPolynomial.eval, toTrigPolynomial_spec]
  exact cosinePolynomial_eval₂ q.1 x

/-- The source polynomial's actual angular lift equals the genuine finite
Fourier evaluation, at every real angular vector. -/
theorem toTrigPolynomial_angular {n d : ℕ} (q : PolynomialSpace n d) (theta : Point n) :
    (toTrigPolynomial q).eval (angularPoint theta) = (angularEval q theta : ℂ) := by
  rw [toTrigPolynomial_eval₂]
  simp_rw [cosineCoordinate_angular]
  simp only [angularEval, polyEval, MvPolynomial.eval₂_eq', MvPolynomial.eval_eq',
    Complex.ofRealHom_eq_coe]
  push_cast
  rfl

end

end Paper34.CosineFourierLift
