import Paper20.HeckeSpecialization
import Mathlib.Data.Nat.Choose.Cast

namespace Paper20.HeckeParameterPolynomial
open Polynomial Matrix Finset Paper20.HeckeTraceAlgebra Paper20.HeckeMatrices
open Paper20.HeckeSpecialization Paper20.HalfTwistMatrix Paper20.BraidWalk
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

/-- The exact entrywise quotient (Omega-1)/z. -/
def incrementQuotient (r : ℕ) : Mat r := fun s t => ((fullTwist r-1) s t).divX

theorem fullTwist_decompose (r : ℕ) (hr : 1 ≤ r) :
    fullTwist r=1+(Polynomial.X:ℤ[X]) • incrementQuotient r := by
  classical
  apply Matrix.ext
  intro s t
  have hc : ((fullTwist r-1) s t).coeff 0=0 := by
    have he : specialize r (fullTwist r-1)=0 := by
      rw [map_sub,specialize_fullTwist r hr,map_one,sub_self]
    have hs := congrFun (congrFun he s) t
    simpa only [specialize_apply,Matrix.zero_apply] using hs

  have hd := X_mul_divX_add ((fullTwist r-1) s t)
  rw [hc,map_zero,add_zero] at hd
  change fullTwist r s t=(1:Mat r) s t+X*((fullTwist r-1) s t).divX
  rw [hd]
  simp

lemma power_binomial (r n : ℕ) (hr : 1 ≤ r) :
    fullTwist r^n=∑ j ∈ range (n+1), n.choose j •
      ((Polynomial.X:ℤ[X])^j • incrementQuotient r^j) := by
  rw [fullTwist_decompose r hr,add_comm]
  have he := (Commute.one_right ((Polynomial.X:ℤ[X]) • incrementQuotient r)).add_pow' n
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at he
  simpa only [one_pow,mul_one,_root_.smul_pow] using he

lemma entry_coeff_binomial (r n m : ℕ) (hr : 1 ≤ r) (s t : State r) :
    ((fullTwist r^n) s t).coeff m=
      ∑ j ∈ range (n+1), (n.choose j:ℤ)*
        (if j ≤ m then ((incrementQuotient r^j) s t).coeff (m-j) else 0) := by
  rw [power_binomial r n hr]
  simp only [Matrix.sum_apply,finset_sum_coeff]
  apply sum_congr rfl
  intro j hj
  change ((n.choose j) • (X^j*((incrementQuotient r^j) s t))).coeff m=_
  rw [coeff_smul,nsmul_eq_mul,coeff_X_pow_mul']

lemma sum_range_truncate {R : Type*} [AddCommMonoid R] (f : ℕ → R) (n m : ℕ)
    (hn : ∀ j, n < j → f j=0) (hm : ∀ j, m < j → f j=0) :
    ∑ j ∈ range (n+1), f j=∑ j ∈ range (m+1), f j := by
  let N := max n m
  have he (a : ℕ) (ha : a ≤ N) (hz : ∀ j, a < j → f j=0) :
      ∑ j ∈ range (a+1), f j=∑ j ∈ range (N+1), f j := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro j hj hja
    apply hz j
    have hge : ¬j < a+1 := by simpa only [mem_range] using hja
    omega
  exact (he n (le_max_left ..) hn).trans (he m (le_max_right ..) hm).symm

/-- A finite binomial expression in the contact exponent, with a bound
independent of that exponent, derived directly from the actual full twist. -/
theorem entry_coeff_finite (r n m : ℕ) (hr : 1 ≤ r) (s t : State r) :
    ((fullTwist r^n) s t).coeff m=
      ∑ j ∈ range (m+1), (n.choose j:ℤ)*
        ((incrementQuotient r^j) s t).coeff (m-j) := by
  rw [entry_coeff_binomial r n m hr s t]
  let f := fun j => (n.choose j:ℤ)*
    (if j ≤ m then ((incrementQuotient r^j) s t).coeff (m-j) else 0)
  have he := sum_range_truncate f n m
    (by intro j hj; simp [f,Nat.choose_eq_zero_of_lt hj])
    (by intro j hj; simp [f,show ¬j ≤ m by omega])
  change (∑ j ∈ range (n+1), f j)=_
  rw [he]
  apply sum_congr rfl
  intro j hj
  dsimp only [f]
  rw [if_pos (by have := mem_range.mp hj; omega)]

/-- The rational polynomial interpolating the actual identity coefficient
of Omega^n, constructed without any partition or spectral formula. -/
def exponentPolynomial (r m : ℕ) : ℚ[X] :=
  ∑ j ∈ range (m+1),
    C ((((incrementQuotient r^j) 1 1).coeff (m-j):ℚ)/(j.factorial:ℚ))*
      descPochhammer ℚ j

theorem exponentPolynomial_eval (r m n : ℕ) (hr : 1 ≤ r) :
    (exponentPolynomial r m).eval (n:ℚ)=(((fullTwist r^n) 1 1).coeff m:ℚ) := by
  rw [entry_coeff_finite r n m hr 1 1]
  simp only [exponentPolynomial,eval_finset_sum,eval_mul,eval_C,Int.cast_sum,Int.cast_mul,Int.cast_natCast]
  apply sum_congr rfl
  intro j hj
  rw [Nat.cast_choose_eq_descPochhammer_div ℚ n j]
  ring

theorem exponentPolynomial_natDegree (r m : ℕ) :
    (exponentPolynomial r m).natDegree ≤ m := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  calc
    _ ≤ (descPochhammer ℚ j).natDegree := Polynomial.natDegree_C_mul_le _ _
    _ = j := descPochhammer_natDegree ℚ j
    _ ≤ m := by have := mem_range.mp hj; omega

/-- Polynomial dependence of every genuine closed-walk coefficient on k,
with degree at most 2h, before the stronger k(k+1) symmetry is used. -/
theorem walkCount_exponent_polynomial (r h k : ℕ) (hr : 1 ≤ r) :
    (exponentPolynomial r (2*h)).eval (k+1:ℚ)=(walkCount r k h:ℚ) := by
  have he := exponentPolynomial_eval r (2*h) (k+1) hr
  rw [Paper20.HeckeFullTwistTrace.fullTwist_identity_coeff r k h hr] at he
  simpa only [Nat.cast_add,Nat.cast_one,Int.cast_natCast] using he

end
end Paper20.HeckeParameterPolynomial
