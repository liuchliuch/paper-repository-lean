import Paper12.WireSupport
import Paper12.StateVectors

noncomputable section
namespace Paper12
open Matrix Classical
variable {J : Type*} [Fintype J]
local instance : DecidableEq (J ⊕ Fin 1) := Classical.decEq _

theorem apply_involutive_matrix (f : Basis J → Basis J) (hf : Function.Involutive f)
    (ψ : Vec J) (b : Basis J) :
    applyOp (fun i j => if f j = i then (1 : ℂ) else 0) ψ b = ψ (f b) := by
  unfold applyOp
  rw [Finset.sum_eq_single (f b)]
  · change (if f (f b) = b then (1 : ℂ) else 0) * ψ (f b) = _
    rw [if_pos (hf b), one_mul]
  · intro a _ ha
    have hn : f a ≠ b := by
      intro h
      have hh := congrArg f h
      rw [hf a] at hh
      exact ha hh
    change (if f a = b then (1 : ℂ) else 0) * ψ a = 0
    rw [if_neg hn, zero_mul]
  · intro hb; exact (hb (Finset.mem_univ _)).elim

theorem equalityAct_involutive (g : Threshold J) : Function.Involutive (equalityAct g) := by
  intro b
  have hw : (∑ x ∈ g.controls, (equalityAct g b x : ℕ)) =
      ∑ x ∈ g.controls, (b x : ℕ) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [← equalityAct_expansion, g.act_control _ hx,
      (nextThreshold g).act_control b (by exact hx)]
  unfold equalityAct
  unfold equalityAct at hw
  rw [hw]
  by_cases ht : (∑ x ∈ g.controls, (b x : ℕ)) = g.threshold
  · simp only [if_pos ht]
    funext x
    by_cases hx : x = g.head
    · subst x; simp
    · simp [hx]
  · simp [ht]

theorem equalityCircuit_apply (g : Threshold J) (ψ : Vec J) (b : Basis J) :
    applyOp (equalityCircuit g).unitary ψ b = ψ (equalityAct g b) := by
  rw [equalityCircuit_unitary]
  exact apply_involutive_matrix _ (equalityAct_involutive g) ψ b

def signedKet (c : ℂ) : Vec (Fin 1) := fun b => if b 0 = 0 then c else -c

theorem signedKet_flip (c : ℂ) (b : Basis (Fin 1)) :
    signedKet c (Function.update b 0 (1 - b 0)) = -signedKet c b := by
  unfold signedKet
  simp only [Function.update_self]
  generalize hv : b 0 = v
  fin_cases v <;> simp

def flagEquality (S : Finset J) (t : ℕ) : Threshold (J ⊕ Fin 1) where
  head := Sum.inr 0
  controls := S.map Function.Embedding.inl
  threshold := t
  head_not := by simp

def phaseOn (p : Basis J → Prop) (ψ : Vec J) : Vec J :=
  fun b => if p b then -ψ b else ψ b

def phaseMatrix (p : Basis J → Prop) : Op J :=
  Matrix.diagonal (fun b => if p b then -1 else 1)

theorem phaseMatrix_apply (p : Basis J → Prop) (ψ : Vec J) :
    applyOp (phaseMatrix p) ψ = phaseOn p ψ := by
  funext b
  simp only [applyOp, phaseMatrix, Matrix.diagonal_apply, phaseOn]
  rw [Finset.sum_eq_single b]
  · by_cases hp : p b <;> simp [hp]
  · intro a _ ha; simp [Ne.symm ha]
  · intro hb; exact (hb (Finset.mem_univ _)).elim

theorem phaseMatrix_reflect (p : Basis J → Prop) : phaseMatrix p = reflect (predicateProjector p) := by
  ext i j
  simp only [phaseMatrix, reflect, predicateProjector, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst j; by_cases hp : p i <;> norm_num [hp]
  · simp [hij]

theorem equality_kickback (S : Finset J) (t : ℕ) (ψ : Vec J) (c : ℂ) :
    applyOp (equalityCircuit (flagEquality S t)).unitary (registerVec ψ (signedKet c)) =
      registerVec (phaseOn (fun b => (∑ x ∈ S, (b x : ℕ)) = t) ψ) (signedKet c) := by
  funext b
  rw [equalityCircuit_apply]
  simp only [equalityAct, flagEquality, Finset.sum_map, Function.Embedding.inl_apply]
  by_cases ht : (∑ x ∈ S, (b (Sum.inl x) : ℕ)) = t
  · simp only [if_pos ht]
    have hL : Function.update b (Sum.inr 0) (1 - b (Sum.inr 0)) ∘ Sum.inl = b ∘ Sum.inl := by
      funext x; simp
    have hR : Function.update b (Sum.inr 0) (1 - b (Sum.inr 0)) ∘ Sum.inr =
        Function.update (b ∘ Sum.inr) 0 (1 - b (Sum.inr 0)) := by
      funext x
      have hx : x = 0 := Fin.eq_zero x
      subst x; simp
    have hp := congrArg ψ hL
    have hk := (congrArg (signedKet c) hR).trans (signedKet_flip c (b ∘ Sum.inr))
    simp only [registerVec, phaseOn, Function.comp_apply, if_pos ht]
    simpa only [mul_neg, neg_mul] using
      congrArg₂ (fun a b : ℂ => a * b) hp hk
  · simp only [if_neg ht, registerVec, phaseOn, Function.comp_apply]

/-- Exact simulation on the fixed kickback state. -/
def KickbackSimulates (c : ℂ) (A : Op (J ⊕ Fin 1)) (B : Op J) : Prop :=
  ∀ ψ : Vec J, applyOp A (registerVec ψ (signedKet c)) =
    registerVec (applyOp B ψ) (signedKet c)

theorem KickbackSimulates.mul {c : ℂ} {A A' : Op (J ⊕ Fin 1)} {B B' : Op J}
    (h : KickbackSimulates c A B) (h' : KickbackSimulates c A' B') :
    KickbackSimulates c (A * A') (B * B') := by
  intro ψ
  rw [applyOp_mul, h', h, ← applyOp_mul]

theorem KickbackSimulates.power {c : ℂ} {A : Op (J ⊕ Fin 1)} {B : Op J}
    (h : KickbackSimulates c A B) (k : ℕ) : KickbackSimulates c (A ^ k) (B ^ k) := by
  induction k with
  | zero => intro ψ; simp
  | succ k ih => simpa only [pow_succ'] using h.mul ih

theorem KickbackSimulates.adjoint {c : ℂ} {A : Op (J ⊕ Fin 1)} {B : Op J}
    (hA : Aᴴ * A = 1) (hB : Bᴴ * B = 1) (h : KickbackSimulates c A B) :
    KickbackSimulates c Aᴴ Bᴴ := by
  intro ψ
  have hb : B * Bᴴ = 1 := Matrix.mul_eq_one_comm.mp hB
  have hh := congrArg (applyOp Aᴴ) (h (applyOp Bᴴ ψ))
  rw [← applyOp_mul, hA, applyOp_one, ← applyOp_mul, hb, applyOp_one] at hh
  exact hh.symm

theorem kickback_extendLeft (c : ℂ) (A : Op J) :
    KickbackSimulates c (extendLeft A) A := by
  intro ψ
  exact (registerTensor_apply A 1 ψ (signedKet c)).trans (by rw [applyOp_one])

theorem kickback_equality (c : ℂ) (S : Finset J) (t : ℕ) :
    KickbackSimulates c (equalityCircuit (flagEquality S t)).unitary
      (phaseMatrix (fun b => (∑ x ∈ S, (b x : ℕ)) = t)) := by
  intro ψ
  rw [equality_kickback, phaseMatrix_apply]
end Paper12
