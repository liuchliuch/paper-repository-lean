import Verification.Objects

namespace P20Objects
open Finset
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

lemma swap_support_injective {r : ℕ} (p q : Equiv.Perm (Fin r))
    (hp : p.IsSwap) (hq : q.IsSwap) (hs : p.support=q.support) : p=q := by
  classical
  rcases hp with ⟨a,b,hab,rfl⟩
  rcases hq with ⟨c,d,hcd,rfl⟩
  rw [Equiv.Perm.support_swap hab,Equiv.Perm.support_swap hcd] at hs
  have ha : a=c ∨ a=d := by
    have hm : a ∈ ({c,d}:Finset (Fin r)) := by rw [← hs]; simp
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hm
  have hb : b=c ∨ b=d := by
    have hm : b ∈ ({c,d}:Finset (Fin r)) := by rw [← hs]; simp
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hm
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  all_goals first | exact False.elim (hab rfl) | rfl | exact Equiv.swap_comm _ _

def supportMap (r : ℕ) (p : Transposition r) : {s : Finset (Fin r) // s.card=2} :=
  ⟨p.val.support,Equiv.Perm.card_support_eq_two.mpr p.property⟩

lemma supportMap_bijective (r : ℕ) : Function.Bijective (supportMap r) := by
  classical
  constructor
  · intro p q h
    apply Subtype.ext
    exact swap_support_injective p.val q.val p.property q.property (congrArg Subtype.val h)
  · intro s
    obtain ⟨a,b,hab,hs⟩ := Finset.card_eq_two.mp s.property
    refine ⟨⟨Equiv.swap a b,⟨a,b,hab,rfl⟩⟩,?_⟩
    apply Subtype.ext
    exact (Equiv.Perm.support_swap hab).trans hs.symm

def transpositionSupportEquiv (r : ℕ) :
    Transposition r ≃ {s : Finset (Fin r) // s.card=2} :=
  Equiv.ofBijective (supportMap r) (supportMap_bijective r)

def twoSubsetEquiv (r : ℕ) :
    {s : Finset (Fin r) // s.card=2} ≃ {s : Finset (Fin r) // s ∈ (univ:Finset (Fin r)).powersetCard 2} where
  toFun s := ⟨s.val,Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,s.property⟩⟩
  invFun s := ⟨s.val,(Finset.mem_powersetCard.mp s.property).2⟩
  left_inv s := Subtype.ext rfl
  right_inv s := Subtype.ext rfl

/-- Actual transpositions are in bijection with unordered two-element
supports, hence their number is binom(r,2). -/
theorem transposition_card (r : ℕ) : Nat.card (Transposition r)=Nat.choose r 2 := by
  classical
  rw [Nat.card_eq_fintype_card]
  calc
    Fintype.card (Transposition r)=
        Fintype.card {s : Finset (Fin r) // s ∈ (univ:Finset (Fin r)).powersetCard 2} :=
      Fintype.card_congr ((transpositionSupportEquiv r).trans (twoSubsetEquiv r))
    _ = _ := by rw [Fintype.card_coe,Finset.card_powersetCard,Finset.card_univ,Fintype.card_fin]

lemma transposition_square (r : ℕ) (s : Transposition r) : s.val*s.val=1 := by
  rcases s.property with ⟨a,b,hab,he⟩
  rw [he,Equiv.swap_mul_self]

lemma return_two_eq (r : ℕ) (w : Fin 2 → Transposition r)
    (hw : (List.ofFn (fun i => (w i).val)).prod=1) : w 1=w 0 := by
  have he : (w 0).val*(w 1).val=1 := by simpa [List.ofFn_succ] using hw
  apply Subtype.ext
  apply mul_left_cancel (a:=(w 0).val)
  exact he.trans (transposition_square r (w 0)).symm

def twoReturnEquiv (r : ℕ) :
    {w : Fin 2 → Transposition r // (List.ofFn (fun i => (w i).val)).prod=1} ≃ Transposition r where
  toFun w := w.val 0
  invFun s := ⟨fun _ => s,by simpa [List.ofFn_succ] using transposition_square r s⟩
  left_inv w := by
    apply Subtype.ext
    funext i
    have he := return_two_eq r w.val w.property
    fin_cases i
    · rfl
    · exact he.symm
  right_inv s := rfl

/-- The genuine length-two transposition-return count is binom(r,2). -/
theorem transpositionReturns_one (r : ℕ) : transpositionReturns r 1=Nat.choose r 2 := by
  unfold transpositionReturns
  change Nat.card {w : Fin 2 → Transposition r // (List.ofFn (fun i => (w i).val)).prod=1}=_
  rw [Nat.card_congr (twoReturnEquiv r),transposition_card]

end
end P20Objects
