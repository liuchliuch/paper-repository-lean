import Mathlib

/-! The sign-convention argument in Remark 2.1, for any normalized HOMFLY
skein system. Link construction and the standard uniqueness theorem of
HOMFLY remain external; the sign transformation is proved here. -/
namespace Paper20.SkeinParity
set_option maxHeartbeats 1000000

structure System (L I : Type*) where
  unknot : L
  plus : I → L
  minus : I → L
  smoothing : I → L
  components : L → ℕ
  components_pos : ∀ l, 1 ≤ components l
  unknot_components : components unknot=1
  crossing_components : ∀ i, components (minus i)=components (plus i)
  smoothing_components : ∀ i,
    components (smoothing i)+1=components (plus i) ∨
      components (plus i)+1=components (smoothing i)

variable {L I K : Type*} [Field K]

def componentSign (S : System L I) (l : L) : K := (-1:K)^(S.components l-1)

structure Law (S : System L I) (a z : K) (P : L → K) : Prop where
  unknot : P S.unknot=1
  skein : ∀ i, a⁻¹*P (S.plus i)-a*P (S.minus i)=z*P (S.smoothing i)

lemma sign_step (n : ℕ) (hn : 1 ≤ n) : (-1:K)^n=-(-1:K)^(n-1) := by
  calc
    (-1:K)^n=(-1:K)^(n-1+1) := congrArg ((-1:K)^·) (by omega)
    _=-(-1:K)^(n-1) := by rw [pow_succ]; ring

lemma sign_smoothing (S : System L I) (i : I) :
    componentSign S (S.smoothing i)=-(componentSign S (S.plus i):K) := by
  unfold componentSign
  rcases S.smoothing_components i with he|he
  · rw [show S.components (S.plus i)-1=S.components (S.smoothing i) by omega,
      sign_step _ (S.components_pos _),neg_neg]
  · rw [show S.components (S.smoothing i)-1=S.components (S.plus i) by omega,
      sign_step _ (S.components_pos _)]

/-- Multiplying the invariant in the opposite z convention by the
component sign preserves both the stated skein relation and unknot value. -/
theorem transformed_law (S : System L I) (a z : K) (Q : L → K)
    (hQ : Law S a (-z) Q) :
    Law S a z (fun l => componentSign S l*Q l) := by
  constructor
  · simp only [componentSign,S.unknot_components,Nat.sub_self,pow_zero,one_mul]
    exact hQ.unknot
  · intro i
    have hm : (componentSign S (S.minus i):K)=componentSign S (S.plus i) := by
      simp only [componentSign,S.crossing_components]
    rw [hm,sign_smoothing]
    calc
      _=componentSign S (S.plus i)*(a⁻¹*Q (S.plus i)-a*Q (S.minus i)) := by ring
      _=componentSign S (S.plus i)*((-z)*Q (S.smoothing i)) := by rw [hQ.skein]
      _=_ := by ring

/-- Uniqueness of the normalized HOMFLY skein invariant gives precisely
P(a,-z)=(-1)^(b-1) P(a,z), in the equivalent oriented form used in (7).
The transformation itself does not assume this parity conclusion. -/
theorem convention_sign (S : System L I) (a z : K)
    (unique : ∀ P Q : L → K, Law S a z P → Law S a z Q → P=Q)
    (P Q : L → K) (hP : Law S a z P) (hQ : Law S a (-z) Q) :
    P=(fun l => componentSign S l*Q l) :=
  unique _ _ hP (transformed_law S a z Q hQ)

end Paper20.SkeinParity
