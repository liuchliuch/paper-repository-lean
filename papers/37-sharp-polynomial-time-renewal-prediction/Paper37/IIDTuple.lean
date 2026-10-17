import Paper37.IIDAddOne
import Paper37.KnownSupportWord

/-! Exact finite-product transport and latest-takeSample marginalization for iid
backward samples, connecting H.1 with the shared equilibrium-cycle interface. -/
noncomputable section
namespace Paper37.IIDTuple
open scoped BigOperators
open Paper37.Compression Paper37.Compression.Distribution Paper37.IIDAddOne

universe u

def toFn {α : Type u} : (n : ℕ) → Sample α n → Fin n → α
  | 0,_ => Fin.elim0
  | n+1,(s,a) => Fin.cases a (toFn n s)

def fromFn {α : Type u} : (n : ℕ) → (Fin n → α) → Sample α n
  | 0,_ => PUnit.unit
  | n+1,ds => (fromFn n (fun i => ds i.succ),ds 0)

lemma fromFn_toFn {α : Type u} (n : ℕ) (s : Sample α n) : fromFn n (toFn n s)=s := by
  induction n with
  | zero => cases s; rfl
  | succ n ih => rcases s with ⟨s,a⟩; simp [fromFn,toFn,ih]

lemma toFn_fromFn {α : Type u} (n : ℕ) (ds : Fin n → α) : toFn n (fromFn n ds)=ds := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp [toFn,fromFn,ih]

def equivFn (α : Type u) (n : ℕ) : Sample α n ≃ (Fin n → α) where
  toFun := toFn n
  invFun := fromFn n
  left_inv := fromFn_toFn n
  right_inv := toFn_fromFn n

lemma iid_toFn_mass {α : Type u} [Fintype α] (p : Distribution α) (n : ℕ) (s : Sample α n) :
    iidLaw p n s = ∏ i, p (toFn n s i) := by
  induction n with
  | zero => cases s; simp [iidLaw,point]
  | succ n ih =>
    rcases s with ⟨s,a⟩
    simp [iidLaw,joint_apply,toFn,Fin.prod_univ_succ,ih,mul_comm]

lemma iidFn_expectation {α : Type u} [Fintype α] (p : Distribution α) (n : ℕ)
    (f : (Fin n → α) → ℝ) :
    (∑ ds : Fin n → α, (∏ i, p (ds i))*f ds) =
      ∑ s, iidLaw p n s*f (toFn n s) := by
  symm
  apply Finset.sum_bij (fun s _ => toFn n s)
  · intro s hs; exact Finset.mem_univ _
  · intro s hs t ht he; exact (equivFn α n).injective he
  · intro ds hds; exact ⟨fromFn n ds,Finset.mem_univ _,toFn_fromFn n ds⟩
  · intro s hs; rw [iid_toFn_mass]

def takeSample {α : Type u} : (k n : ℕ) → k ≤ n → Sample α n → Sample α k
  | 0,_,_,_ => PUnit.unit
  | k+1,0,h,_ => False.elim (Nat.not_succ_le_zero _ h)
  | k+1,n+1,h,(s,a) => (takeSample k n (Nat.le_of_succ_le_succ h) s,a)

lemma iid_prefix_expectation {α : Type u} [Fintype α] (p : Distribution α)
    (k n : ℕ) (h : k ≤ n) (f : Sample α k → ℝ) :
    (∑ s, iidLaw p n s*f (takeSample k n h s)) = ∑ t, iidLaw p k t*f t := by
  induction k generalizing n with
  | zero =>
    change (∑ s, iidLaw p n s*f PUnit.unit) = ∑ t : PUnit, (point PUnit.unit) t*f t
    rw [← Finset.sum_mul,(iidLaw p n).total]
    simp [point]
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n =>
      change (∑ z : Sample α n × α, (iidLaw p n z.1*p z.2)*f (takeSample k n _ z.1,z.2)) =
        ∑ z : Sample α k × α, (iidLaw p k z.1*p z.2)*f z
      rw [Fintype.sum_prod_type,Fintype.sum_prod_type,Finset.sum_comm]
      calc
        _ = ∑ a, p a*(∑ s, iidLaw p n s*f (takeSample k n _ s,a)) := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s hs
          ring
        _ = ∑ a, p a*(∑ t, iidLaw p k t*f (t,a)) := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [ih n (Nat.le_of_succ_le_succ h) (fun t => f (t,a))]
        _ = _ := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro t ht
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a ha
          ring

lemma iidFn_prefix_expectation {α : Type u} [Fintype α] (p : Distribution α)
    (k n : ℕ) (h : k ≤ n) (f : Sample α k → ℝ) :
    (∑ ds : Fin n → α, (∏ i, p (ds i))*f (takeSample k n h (fromFn n ds))) =
      ∑ s, iidLaw p k s*f s := by
  rw [iidFn_expectation]
  simp_rw [fromFn_toFn]
  exact iid_prefix_expectation p k n h f

lemma indices_of_toFn {B : ℕ} (n : ℕ) (s : Sample (Fin B) n) :
    List.ofFn (fun i => (toFn n s i).val) = Paper37.KnownSupportWord.sampleIndices n s := by
  induction n with
  | zero => rfl
  | succ n ih => rcases s with ⟨s,a⟩; simp [toFn,List.ofFn_succ,ih,Paper37.KnownSupportWord.sampleIndices]

lemma prefix_indices {B : ℕ} (k n : ℕ) (h : k ≤ n) (s : Sample (Fin B) n) :
    Paper37.KnownSupportWord.sampleIndices k (takeSample k n h s) =
      (Paper37.KnownSupportWord.sampleIndices n s).take k := by
  induction k generalizing n with
  | zero => simp [takeSample,Paper37.KnownSupportWord.sampleIndices]
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n =>
      rcases s with ⟨s,a⟩
      simp [takeSample,Paper37.KnownSupportWord.sampleIndices,ih]

end Paper37.IIDTuple
