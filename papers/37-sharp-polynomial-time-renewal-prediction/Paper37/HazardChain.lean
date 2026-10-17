import Paper37.Boundary
import Paper37.Compression
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! The exact finite-support survival/hazard KL decomposition used in H.3. -/
noncomputable section
namespace Paper37.HazardChain
open Paper37.Boundary

lemma weighted_log_div {x c : ℝ} (_hx : 0 ≤ x) (hc : 0 < c) :
    x*Real.log (x/c) = x*Real.log x-x*Real.log c := by
  by_cases he : x=0
  · simp [he]
  · rw [Real.log_div he hc.ne']; ring

lemma weighted_log_mul_div {x c d : ℝ} (_hx : 0 ≤ x) (hc : 0 < c) (hd : 0 < d) :
    x*Real.log (x*c/d) = x*Real.log x+x*Real.log c-x*Real.log d := by
  by_cases he : x=0
  · simp [he]
  · rw [Real.log_div (mul_ne_zero he hc.ne') hd.ne', Real.log_mul he hc.ne']; ring

/-- Binary splitting of unnormalized positive prediction masses, including
zero target cells. This is the local identity that telescopes along survival. -/
theorem binary_split {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 < c) (hd : 0 < d) :
    (a+b)*klReal (a/(a+b)) (c/(c+d)) =
      a*Real.log (a/c)+b*Real.log (b/d)-(a+b)*Real.log ((a+b)/(c+d)) := by
  have hcd : 0 < c+d := by linarith
  by_cases hab : a+b=0
  · have ha0 : a=0 := by linarith
    have hb0 : b=0 := by linarith
    simp [ha0,hb0]
  have habp : 0 < a+b := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hab)
  have hsubp : 1-a/(a+b)=b/(a+b) := by field_simp; ring
  have hsubq : 1-c/(c+d)=d/(c+d) := by field_simp; ring
  have hra : (a/(a+b))/(c/(c+d)) = a*(c+d)/((a+b)*c) := by field_simp
  have hrb : (b/(a+b))/(d/(c+d)) = b*(c+d)/((a+b)*d) := by field_simp
  rw [klReal, hsubp, hsubq, hra, hrb]
  have hfactor : (a+b)*(a/(a+b)*Real.log (a*(c+d)/((a+b)*c))+
      b/(a+b)*Real.log (b*(c+d)/((a+b)*d))) =
      a*Real.log (a*(c+d)/((a+b)*c))+b*Real.log (b*(c+d)/((a+b)*d)) := by
    field_simp
  rw [hfactor, weighted_log_mul_div ha hcd (mul_pos habp hc),
    weighted_log_mul_div hb hcd (mul_pos habp hd),
    weighted_log_div ha hc, weighted_log_div hb hd,
    weighted_log_div habp.le hcd,
    Real.log_mul habp.ne' hc.ne', Real.log_mul habp.ne' hd.ne']
  ring

/-- The sum of the survival-weighted Bernoulli divergences over all ages. -/
def hazardKL : List ℝ → List ℝ → ℝ
  | a::as, c::cs => (a+as.sum)*klReal (a/(a+as.sum)) (c/(c+cs.sum)) + hazardKL as cs
  | _,_ => 0

/-- The categorical divergence written in the same positive-length order. -/
def categoricalKL : List ℝ → List ℝ → ℝ
  | a::as,c::cs => a*Real.log (a/c)+categoricalKL as cs
  | _,_ => 0

lemma hazardKL_singleton (a c : ℝ) (_ha : 0 ≤ a) (hc : 0 < c) :
    hazardKL [a] [c] = 0 := by
  by_cases he : a=0
  · simp [hazardKL,he]
  · simp [hazardKL, klReal, div_self he, div_self hc.ne']

/-- The unnormalized survival chain rule. Zero-survival target terms vanish
through their actual survival multiplier, as required by source H.3. -/
theorem hazardKL_telescope (p q : List ℝ) (hlen : p.length=q.length)
    (hp : ∀ a ∈ p, 0 ≤ a) (hq : ∀ c ∈ q, 0 < c) :
    hazardKL p q = categoricalKL p q-p.sum*Real.log (p.sum/q.sum) := by
  induction p generalizing q with
  | nil => cases q <;> simp_all [hazardKL,categoricalKL]
  | cons a p ih =>
    cases q with
    | nil => simp at hlen
    | cons c q =>
      have ha : 0 ≤ a := hp a (by simp)
      have hc : 0 < c := hq c (by simp)
      have hpt : ∀ b ∈ p, 0 ≤ b := fun b hb => hp b (by simp [hb])
      have hqt : ∀ d ∈ q, 0 < d := fun d hd => hq d (by simp [hd])
      have hl : p.length=q.length := by simpa using hlen
      cases q with
      | nil =>
        have hp0 : p=[] := List.length_eq_zero_iff.mp (by simpa using hl)
        subst p
        simp [hazardKL_singleton a c ha hc, categoricalKL]
      | cons d q =>
        have hsumq : 0 < (d::q).sum := by
          exact List.sum_pos (d::q) hqt (by simp)
        have hsump : 0 ≤ p.sum := List.sum_nonneg hpt
        have hb := binary_split ha hsump hc hsumq
        rw [hazardKL, ih (d::q) hl hpt hqt, categoricalKL]
        simp only [List.sum_cons]
        simp only [List.sum_cons] at hb
        linarith

/-- Exact hazard chain rule H.3 for two finite probability vectors with a
full-support predicted vector. No hazard identity is assumed as an input. -/
theorem hazardKL_eq_categoricalKL (p q : List ℝ) (hlen : p.length=q.length)
    (hp : ∀ a ∈ p, 0 ≤ a) (hq : ∀ c ∈ q, 0 < c)
    (hp1 : p.sum=1) (hq1 : q.sum=1) :
    hazardKL p q = categoricalKL p q := by
  rw [hazardKL_telescope p q hlen hp hq,hp1,hq1]
  simp


open scoped BigOperators
open Paper37.Compression Paper37.Compression.Distribution

/-- Survival of a finite positive-gap vector at age a. -/
def survival {B : ℕ} (p : Fin B → ℝ) (a : ℕ) : ℝ := ((List.ofFn p).drop a).sum

lemma categoricalKL_ofFn {B : ℕ} (p q : Fin B → ℝ) :
    categoricalKL (List.ofFn p) (List.ofFn q) = ∑ a, p a*Real.log (p a/q a) := by
  induction B with
  | zero => simp [categoricalKL]
  | succ B ih =>
    rw [List.ofFn_succ, List.ofFn_succ, categoricalKL, ih, Fin.sum_univ_succ]

lemma hazardKL_ofFn {B : ℕ} (p q : Fin B → ℝ) :
    hazardKL (List.ofFn p) (List.ofFn q) =
      ∑ a, survival p a.val * klReal (p a/survival p a.val) (q a/survival q a.val) := by
  induction B with
  | zero => simp [hazardKL]
  | succ B ih =>
    rw [List.ofFn_succ, List.ofFn_succ, hazardKL, ih, Fin.sum_univ_succ]
    simp only [survival, List.ofFn_succ, Fin.val_zero, List.drop_zero, List.sum_cons,
      Fin.val_succ, List.drop_succ_cons]

/-- The exact finite-support hazard chain rule, equation H.3. The target law
may have zero mass or zero survival; those terms carry their actual zero weight. -/
theorem finite_hazard_chain_rule {B : ℕ} (p q : Distribution (Fin B))
    (hq : ∀ a, 0 < q a) :
    (∑ a, survival p a.val * klReal (p a/survival p a.val) (q a/survival q a.val)) =
      Distribution.kl p q := by
  rw [← hazardKL_ofFn]
  have hpList : ∀ z ∈ List.ofFn p, 0 ≤ z := by
    intro z hz
    obtain ⟨a,rfl⟩ := List.mem_ofFn.mp hz
    exact p.nonneg a
  have hqList : ∀ z ∈ List.ofFn q, 0 < z := by
    intro z hz
    obtain ⟨a,rfl⟩ := List.mem_ofFn.mp hz
    exact hq a
  have hlen : (List.ofFn p).length=(List.ofFn q).length := by simp
  have hpsum : (List.ofFn p).sum=1 := by rw [List.sum_ofFn]; exact p.total
  have hqsum : (List.ofFn q).sum=1 := by rw [List.sum_ofFn]; exact q.total
  rw [hazardKL_eq_categoricalKL _ _ hlen hpList hqList hpsum hqsum, categoricalKL_ofFn]
  unfold Distribution.kl
  apply Finset.sum_congr rfl
  intro a ha
  simpa only [mul_sub] using weighted_log_div (p.nonneg a) (hq a)

end Paper37.HazardChain
