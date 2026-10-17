import Paper08.RationalQuadrature
import Paper08.ZeroFree
import Paper08.MultiMoments
import Paper08.Moments
import Mathlib.Algebra.Order.Antidiag.Finsupp
import Mathlib.Data.Finsupp.Weight

/-! # Executable B-local primitive and ordinary moments

The programs inspect scopes and invoke value queries; they never evaluate real
factor functions or integrals. Zero exponents are removed before quadrature.
-/
open scoped BigOperators
namespace Paper08.PrimitiveMomentsQ

abbrev Queries {n m : ℕ} (scopes : Fin m → Finset (Fin n)) :=
  (e : Fin m) → (Fin (scopes e).card → ℚ) → ℕ → ℚ

def primitiveQ {n m : ℕ} (scopes : Fin m → Finset (Fin n)) (query : Queries scopes)
    (d : Fin m →₀ ℕ) (s C : ℕ) (τ : ℚ) : ℚ :=
  RationalQuadrature.primitiveRuleQ
    (fun i : Fin d.support.card => scopes (d.support.orderEmbOfFin rfl i))
    (fun i => query (d.support.orderEmbOfFin rfl i))
    (fun i => d (d.support.orderEmbOfFin rfl i)) s C τ

def factorialWeight {m : ℕ} (d : Fin m →₀ ℕ) : ℕ :=
  d.prod (fun _ a => a.factorial)

/-- Actual finite multinomial moment program, with the constant moment exactly one. -/
def momentQ {n m : ℕ} (scopes : Fin m → Finset (Fin n)) (query : Queries scopes)
    (B : Finset (Fin m)) (j s C : ℕ) (τ : ℚ) : ℚ :=
  if j = 0 then 1 else
    ∑ d ∈ Finset.finsuppAntidiag B j, primitiveQ scopes query d s C τ / factorialWeight d

@[simp] theorem momentQ_zero {n m : ℕ} (scopes : Fin m → Finset (Fin n))
    (query : Queries scopes) (B : Finset (Fin m)) (s C : ℕ) (τ : ℚ) :
    momentQ scopes query B 0 s C τ = 1 := by simp [momentQ]

@[simp] theorem momentQ_empty {n m j : ℕ} (scopes : Fin m → Finset (Fin n))
    (query : Queries scopes) (hj : j ≠ 0) (s C : ℕ) (τ : ℚ) :
    momentQ scopes query ∅ j s C τ = 0 := by simp [momentQ, hj]

noncomputable section
open MeasureTheory

def primitive {n r m : ℕ} (E : FactorFamily n r m) (d : Fin m →₀ ℕ) : ℝ :=
  Integral.cubeIntegral (fun x => ∏ e, ZeroFree.ell (E e) x ^ d e)

lemma integrand_sparse {n r m : ℕ} (E : FactorFamily n r m) (d : Fin m →₀ ℕ)
    (x : Fin n → ℝ) :
    (∏ i : Fin d.support.card,
      ZeroFree.ell (E (d.support.orderEmbOfFin rfl i)) x ^
        d (d.support.orderEmbOfFin rfl i)) = ∏ e, ZeroFree.ell (E e) x ^ d e := by
  rw [TupleCount.prod_ordered d.support (fun e => ZeroFree.ell (E e) x ^ d e)]
  apply Finset.prod_subset (Finset.subset_univ _)
  intro e _ he
  simp [Finsupp.notMem_support_iff.mp he]

/-- The primitive program approximates the original ambient primitive integral. -/
theorem primitiveQ_error {n r m s C : ℕ} (E : FactorFamily n r m)
    (O : (e : Fin m) → Oracle.Oracle (E e).scope.card (E e).psi.toFun)
    (d : Fin m →₀ ℕ) (hd : d.degree ≤ s) (hs : 1 ≤ s)
    {q K : ℝ} (hq : 0 ≤ q) (hqthird : q < 1 / 3) (hK : 0 ≤ K)
    (hE : ∀ e, (E e).RangeOk q) (hLip : ∀ e, (E e).LipOk K)
    (hC : 2 ≤ C) (hqC : 2 * q ≤ (C : ℝ)) (hKC : 6 * Real.sqrt r * K ≤ (C : ℝ))
    (τ : ℚ) (hτ : 0 < τ) :
    |(primitiveQ (fun e => (E e).scope) (fun e => (O e).query) d s C τ : ℝ) -
      primitive E d| ≤ (τ : ℝ) := by
  have hsum : (∑ i : Fin d.support.card, d (d.support.orderEmbOfFin rfl i)) ≤ s := by
    rw [TupleCount.sum_ordered]
    exact hd
  have he := RationalQuadrature.primitiveRuleQ_error
    (fun i : Fin d.support.card => (E (d.support.orderEmbOfFin rfl i)).scope)
    (fun i => (E _).card_le)
    (fun i => (E (d.support.orderEmbOfFin rfl i)).psi)
    (fun i => O (d.support.orderEmbOfFin rfl i))
    (fun i => d (d.support.orderEmbOfFin rfl i))
    (fun i => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp
      (d.support.orderEmbOfFin_mem rfl i))) hsum hs hq hqthird hK
    (fun i x hx => ⟨(hE _).2 x (Integral.mem_cube.mp hx),
      (le_abs_self _).trans ((hE _).1 x (Integral.mem_cube.mp hx))⟩)
    (fun i => hLip _) hC hqC hKC τ hτ
  convert he using 1
  congr 2
  unfold primitive
  congr 1
  funext x
  exact (integrand_sparse E d x).symm

lemma factorialWeight_pos {m : ℕ} (d : Fin m →₀ ℕ) : 0 < factorialWeight d := by
  unfold factorialWeight Finsupp.prod
  exact Finset.prod_pos fun e _ => Nat.factorial_pos _

lemma factorialWeight_cast {m : ℕ} (d : Fin m →₀ ℕ) :
    (factorialWeight d : ℝ) = d.prod (fun _ a => (a.factorial : ℝ)) := by
  simp [factorialWeight, Finsupp.prod]

def multinomialMoment {n r m : ℕ} (E : FactorFamily n r m)
    (B : Finset (Fin m)) (j : ℕ) : ℝ :=
  ∑ d ∈ Finset.finsuppAntidiag B j, primitive E d / (factorialWeight d : ℝ)

theorem realMoment_eq_multinomial {n r m : ℕ} (E : FactorFamily n r m)
    (B : Finset (Fin m)) {q K : ℝ}
    (hE : ∀ e ∈ B, (E e).RangeOk q) (hLip : ∀ e ∈ B, (E e).LipOk K) (j : ℕ) :
    MomentSeries.realMoment E B j = multinomialMoment E B j := by
  have heq : multinomialMoment E B j =
      ∑ d ∈ Finset.finsuppAntidiag B j,
        MultiMoments.primitive E d / d.prod (fun _ a => (a.factorial : ℝ)) := by
    unfold multinomialMoment
    simp only [factorialWeight_cast]
    rfl
  rw [heq]
  apply Complex.ofReal_injective
  rw [MomentSeries.ofReal_realMoment, MultiMoments.moment_eq_sum_primitive E B hE hLip j]
  push_cast
  rfl

/-- The actual B-local moment program satisfies the complete error estimate
following (4.2), using the true integral moments rather than a moment certificate. -/
theorem momentQ_error {n r m s C j : ℕ} (E : FactorFamily n r m)
    (O : (e : Fin m) → Oracle.Oracle (E e).scope.card (E e).psi.toFun)
    (B : Finset (Fin m)) (hB : B.card ≤ s) (hj : j ≤ s) (hs : 1 ≤ s)
    {q K : ℝ} (hq : 0 ≤ q) (hqthird : q < 1 / 3) (hK : 0 ≤ K)
    (hE : ∀ e, (E e).RangeOk q) (hLip : ∀ e, (E e).LipOk K)
    (hC : 2 ≤ C) (hqC : 2 * q ≤ (C : ℝ)) (hKC : 6 * Real.sqrt r * K ≤ (C : ℝ))
    (τ : ℚ) (hτ : 0 < τ) :
    |(momentQ (fun e => (E e).scope) (fun e => (O e).query) B j s C τ : ℝ) -
      MomentSeries.realMoment E B j| ≤ (4 : ℝ) ^ s * (τ : ℝ) := by
  by_cases hj₀ : j = 0
  · subst j
    simp only [momentQ_zero, Rat.cast_one, MomentSeries.realMoment_zero, sub_self, abs_zero]
    positivity
  rw [realMoment_eq_multinomial E B (fun e _ => hE e) (fun e _ => hLip e) j]
  let I := primitive E
  let Ihat := fun d : Fin m →₀ ℕ =>
    (primitiveQ (fun e => (E e).scope) (fun e => (O e).query) d s C τ : ℝ)
  let w := fun d : Fin m →₀ ℕ => (factorialWeight d : ℝ)⁻¹
  have hw : ∀ d ∈ Finset.finsuppAntidiag B j, |w d| ≤ 1 := by
    intro d _
    have hpos : (0 : ℝ) < factorialWeight d := by exact_mod_cast factorialWeight_pos d
    have hone : (1 : ℝ) ≤ factorialWeight d := by exact_mod_cast factorialWeight_pos d
    dsimp [w]
    rw [abs_of_pos (inv_pos.mpr hpos)]
    exact (inv_le_one₀ hpos).mpr hone
  have herr : ∀ d ∈ Finset.finsuppAntidiag B j, |Ihat d - I d| ≤ (τ : ℝ) := by
    intro d hd
    have hdeg : d.degree ≤ s := by
      have hh := (Finset.mem_finsuppAntidiag'.mp hd).1
      change (∑ e ∈ d.support, d e) ≤ s
      change (∑ e ∈ d.support, d e) = j at hh
      omega
    exact primitiveQ_error E O d hdeg hs hq hqthird hK hE hLip hC hqC hKC τ hτ
  have h := Moments.moment_error_le (Finset.finsuppAntidiag B j) w I Ihat s
    (τ : ℝ) (by exact_mod_cast hτ.le) (TupleCount.card_finsuppAntidiag_le B hB hj) hw herr
  have hcomputed :
      (momentQ (fun e => (E e).scope) (fun e => (O e).query) B j s C τ : ℝ) =
        ∑ d ∈ Finset.finsuppAntidiag B j, Ihat d / (factorialWeight d : ℝ) := by
    simp [momentQ, hj₀, Ihat]
  rw [hcomputed]
  simpa only [multinomialMoment, w, I, div_eq_mul_inv, mul_comm] using h

end
end Paper08.PrimitiveMomentsQ
