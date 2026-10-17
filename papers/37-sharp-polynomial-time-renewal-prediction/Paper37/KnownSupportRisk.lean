import Paper37.IIDAddOne
import Mathlib.Order.Interval.Finset.Fin

/-! Exact H.1 statistical guarantee on the equilibrium-age and iid backward-gap
product law. The source block-law realization is a separate cycle representation. -/
noncomputable section
namespace Paper37.KnownSupportRisk
open scoped BigOperators
open Paper37.Compression Paper37.Compression.Distribution
open Paper37.KnownSupport Paper37.HazardChain Paper37.IIDAddOne

lemma survival_eq_sum {B : ℕ} (p : Fin B → ℝ) (a : ℕ) :
    survival p a = ∑ j, if a ≤ j.val then p j else 0 := by
  induction B generalizing a with
  | zero => simp [survival]
  | succ B ih =>
    cases a with
    | zero => simp [survival,List.sum_ofFn,Fin.sum_univ_succ]
    | succ a =>
      rw [survival,List.ofFn_succ,List.drop_succ_cons]
      change survival (fun j : Fin B => p j.succ) a = _
      rw [ih,Fin.sum_univ_succ]
      simp

/-- The genuine mean positive gap of a finite gap distribution. -/
def finiteMean {B : ℕ} (p : Distribution (Fin B)) : ℝ :=
  ∑ j, ((j.val:ℝ)+1)*p j

lemma finiteMean_ge_one {B : ℕ} (p : Distribution (Fin B)) : 1 ≤ finiteMean p := by
  rw [← p.total]
  apply Finset.sum_le_sum
  intro j hj
  have hn : 0 ≤ (j.val:ℝ) := Nat.cast_nonneg _
  have hm := mul_nonneg hn (p.nonneg j)
  nlinarith

lemma finiteMean_pos {B : ℕ} (p : Distribution (Fin B)) : 0 < finiteMean p :=
  lt_of_lt_of_le zero_lt_one (finiteMean_ge_one p)

lemma survival_nonneg {B : ℕ} (p : Distribution (Fin B)) (a : ℕ) : 0 ≤ survival p a := by
  rw [survival_eq_sum]
  apply Finset.sum_nonneg
  intro j hj
  split_ifs <;> simp_all [p.nonneg]

lemma sum_survival_eq_mean {B : ℕ} (p : Distribution (Fin B)) :
    (∑ a : Fin B, survival p a.val) = finiteMean p := by
  simp_rw [survival_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  have hset : ((Finset.univ:Finset (Fin B)).filter (fun a => a.val ≤ j.val)) = Finset.Iic j := by
    ext a
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Iic]
    rfl
  have hcard : ((Finset.univ:Finset (Fin B)).filter (fun a => a.val ≤ j.val)).card = j.val+1 := by
    rw [hset,Fin.card_Iic]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul]
  rw [hcard]
  push_cast
  rfl

/-- The exact stationary age law: survival at a divided by the mean gap. -/
def ageLaw {B : ℕ} (p : Distribution (Fin B)) : Distribution (Fin B) where
  mass a := survival p a.val/finiteMean p
  nonneg a := div_nonneg (survival_nonneg p a.val) (finiteMean_pos p).le
  total := by rw [← Finset.sum_div,sum_survival_eq_mean]; exact div_self (finiteMean_pos p).ne'

/-- Add-one's hazard at the queried age, computed from the actual iid sample. -/
def estimatedHazard {B : ℕ} [Nonempty (Fin B)] (k : ℕ) (s : Sample (Fin B) k) (a : Fin B) : ℝ :=
  let q := addOne k (fun j => count j k s) (count_sum k s)
  q a/survival q a.val

def trueHazard {B : ℕ} (p : Distribution (Fin B)) (a : Fin B) : ℝ :=
  p a/survival p a.val

/-- Exact H.3 transfer from categorical estimation to stationary-age hazard
estimation, with independent iid samples and their actual add-one estimator. -/
theorem product_hazard_risk_eq {B : ℕ} [Nonempty (Fin B)]
    (p : Distribution (Fin B)) (k : ℕ) :
    (∑ s, iidLaw p k s * ∑ a, ageLaw p a *
      Paper37.Boundary.klReal (trueHazard p a) (estimatedHazard k s a)) =
      (∑ s, iidLaw p k s*Distribution.kl p
        (addOne k (fun j => count j k s) (count_sum k s)))/finiteMean p := by
  calc
    _ = ∑ s, iidLaw p k s *
        (Distribution.kl p (addOne k (fun j => count j k s) (count_sum k s))/finiteMean p) := by
      apply Finset.sum_congr rfl
      intro s hs
      congr 1
      have hq : ∀ a, 0 < addOne k (fun j => count j k s) (count_sum k s) a := by
        intro a
        change 0 < ((count a k s:ℝ)+1)/((k:ℝ)+Fintype.card (Fin B))
        positivity
      have hc := finite_hazard_chain_rule p (addOne k (fun j => count j k s) (count_sum k s)) hq
      rw [← hc]
      dsimp only [ageLaw,trueHazard,estimatedHazard]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = _ := by rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro s hs; ring

/-- The first and sharpest inequality in H.2 for the exact age×iid product law. -/
theorem product_hazard_risk_le {B : ℕ} [Nonempty (Fin B)]
    (p : Distribution (Fin B)) (k : ℕ) :
    (∑ s, iidLaw p k s * ∑ a, ageLaw p a *
      Paper37.Boundary.klReal (trueHazard p a) (estimatedHazard k s a)) ≤
        ((B:ℝ)-1)/(finiteMean p*((k:ℝ)+1)) := by
  rw [product_hazard_risk_eq]
  have hh := div_le_div_of_nonneg_right (iid_addOne_expectedKL_le p k) (finiteMean_pos p).le
  simpa only [Fintype.card_fin,div_div,mul_comm] using hh

/-- All four source H.2 bounds at the prescribed backward sample size, including
B≤n/2, with the mean equal to the actual finite gap mean. -/
theorem product_hazard_risk_bounds {n B : ℕ} [Nonempty (Fin B)]
    (p : Distribution (Fin B)) (hB : 1 ≤ B) (hBn : 2*B ≤ n) :
    let k := n/B-1
    let R := ∑ s, iidLaw p k s * ∑ a, ageLaw p a *
      Paper37.Boundary.klReal (trueHazard p a) (estimatedHazard k s a)
    R ≤ ((B:ℝ)-1)/(finiteMean p*(n/B:ℕ)) ∧
      R ≤ (B:ℝ)*((B:ℝ)-1)/(finiteMean p*((n:ℝ)-B)) ∧
      R ≤ 2*(B:ℝ)^2/(finiteMean p*n) ∧ R ≤ 2*(B:ℝ)^2/n := by
  dsimp
  have hdiv : 1 ≤ n/B := (Nat.le_div_iff_mul_le (by omega : 0 < B)).mpr (by omega)
  have he : (((n/B-1:ℕ):ℝ)+1) = (n/B:ℕ) := by exact_mod_cast (show n/B-1+1=n/B by omega)
  have hmain := product_hazard_risk_le p (n/B-1)
  rw [he] at hmain
  have hc := support_bound_chain hB hBn (finiteMean_ge_one p)
  exact ⟨hmain,hmain.trans hc.1,hmain.trans (hc.1.trans hc.2.1),
    hmain.trans (hc.1.trans (hc.2.1.trans hc.2.2))⟩

end Paper37.KnownSupportRisk
