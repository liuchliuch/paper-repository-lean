import Paper13.PauliSupport
noncomputable section
namespace Paper13
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def gradeToggle (a : Fin 4) : Fin 4 := match a.val with | 0 => 2 | 1 => 3 | 2 => 0 | _ => 1
lemma gradeToggle_involutive : Function.Involutive gradeToggle := by intro a; fin_cases a <;> rfl
lemma gradeToggle_grade (a : Fin 4) : pauliGrade (gradeToggle a)= -pauliGrade a := by fin_cases a <;> rfl

def wordToggle {n : ℕ} (i : Fin n) (w : Fin n → Fin 4) := Function.update w i (gradeToggle (w i))
lemma wordToggle_involutive {n : ℕ} (i : Fin n) : Function.Involutive (wordToggle i) := by
  intro w
  simp [wordToggle,gradeToggle_involutive (w i)]
lemma wordToggle_grade {n : ℕ} (i : Fin n) (w : Fin n → Fin 4) : wordGrade (wordToggle i w)= -wordGrade w := by
  rw [wordToggle,wordGrade_update,gradeToggle_grade,neg_mul,pauliGrade_sq,neg_one_mul]
lemma wordGrade_cases {n : ℕ} (w : Fin n → Fin 4) : wordGrade w=1 ∨ wordGrade w= -1 :=
  mul_self_eq_one_iff.mp (wordGrade_sq w)

def evenOddEquiv {n : ℕ} (i : Fin n) : {w : Fin n → Fin 4 // EvenPauli w} ≃ {w : Fin n → Fin 4 // ¬EvenPauli w} where
  toFun w := ⟨wordToggle i w.val,by change wordGrade _ ≠ 1; rw [wordToggle_grade,w.property]; norm_num⟩
  invFun w := ⟨wordToggle i w.val,by
    change wordGrade _=1
    have h := (wordGrade_cases w.val).resolve_left w.property
    rw [wordToggle_grade,h]; norm_num⟩
  left_inv w := Subtype.ext (wordToggle_involutive i w.val)
  right_inv w := Subtype.ext (wordToggle_involutive i w.val)

/-- Exactly half of the 4^n Pauli words have even Y/Z parity. -/
theorem evenPauli_card (n : ℕ) (hn : 0 < n) :
    Fintype.card {w : Fin n → Fin 4 // EvenPauli w}=2^(2*n-1) := by
  have he := Fintype.card_congr (evenOddEquiv (⟨0,hn⟩ : Fin n))
  rw [Fintype.card_subtype_compl] at he
  have hle := Fintype.card_subtype_le (EvenPauli (n := n))
  have ht : Fintype.card (Fin n → Fin 4)=2*2^(2*n-1) := by
    simp only [Fintype.card_fun,Fintype.card_fin]
    rw [show (4 : ℕ)=2^2 by norm_num,←pow_mul]
    calc
      2^(2*n)=2^((2*n-1)+1) := congrArg (fun t => 2^t) (by omega)
      _ = 2*2^(2*n-1) := by rw [pow_succ,Nat.mul_comm]
  omega

/-- Removing the identity and global X leaves precisely 2^(2n-1)-2 admissible words. -/
theorem admissiblePauli_card (n : ℕ) (hn : 0 < n) :
    Fintype.card {w : Fin n → Fin 4 // AdmissiblePauli w}=2^(2*n-1)-2 := by
  let E := {w : Fin n → Fin 4 // EvenPauli w}
  let z : E := ⟨fun _ => 0,by simp [EvenPauli,wordGrade]⟩
  let x : E := ⟨fun _ => 1,by simp [EvenPauli,wordGrade]⟩
  have hzx : z≠x := by
    intro h
    have h0 := congrArg (fun w : E => w.val ⟨0,hn⟩) h
    change (0 : Fin 4)=1 at h0
    exact (by decide : (0 : Fin 4)≠1) h0
  let e : {w : Fin n → Fin 4 // AdmissiblePauli w} ≃ {w : E // w≠z ∧ w≠x} := {
    toFun := fun w => ⟨⟨w.val,w.property.1⟩,by
      constructor
      · intro h; exact w.property.2.1 (congrArg Subtype.val h)
      · intro h; exact w.property.2.2 (congrArg Subtype.val h)⟩
    invFun := fun w => ⟨w.val.val,⟨w.val.property,
      (fun h => w.property.1 (Subtype.ext h)),(fun h => w.property.2 (Subtype.ext h))⟩⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Fintype.card_congr e,Fintype.card_of_subtype (Finset.univ \ {z,x}) (by intro w; simp)]
  rw [Finset.card_sdiff,Finset.inter_univ,Finset.card_univ,Finset.card_pair hzx]
  exact congrArg (fun t => t-2) (evenPauli_card n hn)
end Paper13
