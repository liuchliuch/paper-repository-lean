import Paper20.StandardExchangeDisjoint

namespace Paper20.YoungShapes
open Paper20.YoungCorners
noncomputable section
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

/-- A genuine valid adjacent exchange between two actual standard
fillings of the same actual Young diagram. -/
def FillingStep {n : ℕ} {μ : Shape n} (t u : StandardFilling μ) : Prop :=
  ∃ i j : Fin n, ∃ h : j.val=i.val+1, ∃ e : Exchangeable t i j, u=exchange t i j h e

abbrev FillingReachable {n : ℕ} {μ : Shape n} :=
  Relation.ReflTransGen (FillingStep (μ:=μ))

lemma filling_not_reverse {n : ℕ} {μ : Shape n} (t : StandardFilling μ)
    (i j : Fin n) (hij : i < j) : ¬t.val j≤t.val i := by
  have he := position_not_reverse (fillingPath n μ t) i j hij
  simpa only [fillingPath_position] using he

/-- An actual maximal cell can move to the last label by genuine adjacent
standard exchanges. At each move every intervening cell is incomparable,
and the exact remaining label distance strictly decreases. -/
theorem filling_move_corner_to_last {n : ℕ} {μ : Shape (n+1)}
    (t : StandardFilling μ) (c : ℕ × ℕ) (hc : Removable μ.val c) :
    ∃ u : StandardFilling μ, FillingReachable t u ∧ (u.val (Fin.last n)).val=c := by
  let cCell : Cells μ.val := ⟨c,hc.1⟩
  have aux : ∀ d : ℕ, ∀ t : StandardFilling μ, n-(t.val.symm cCell).val=d →
      ∃ u : StandardFilling μ, FillingReachable t u ∧ (u.val (Fin.last n)).val=c := by
    intro d
    induction d using Nat.strongRecOn with
    | ind d ih =>
      intro t hd
      let i := t.val.symm cCell
      have hi := i.isLt
      have hd' : n-i.val=d := hd
      by_cases hl : i.val=n
      · have he : i=Fin.last n := Fin.ext hl
        have hc' : t.val i=cCell := t.val.apply_symm_apply cCell
        rw [he] at hc'
        exact ⟨t,Relation.ReflTransGen.refl,congrArg Subtype.val hc'⟩
      · have hil : i.val < n := by omega
        let j : Fin (n+1) := ⟨i.val+1,by omega⟩
        have hij : j.val=i.val+1 := rfl
        have hlt : i < j := by change i.val < i.val+1; omega
        have he : t.val i=cCell := t.val.apply_symm_apply cCell
        have hex : Exchangeable t i j := by
          constructor
          · intro hle
            have hle' : c≤(t.val j).val := by
              have hcv := congrArg Subtype.val he
              change (t.val i).val≤(t.val j).val at hle
              rw [hcv] at hle
              exact hle
            have hcorner := removable_maximal μ.val c hc (t.val j).val (t.val j).property hle'
            have hji : j=i := t.val.injective ((Subtype.ext hcorner).trans he.symm)
            exact (ne_of_lt hlt) hji.symm
          · exact filling_not_reverse t i j hlt
        let u := exchange t i j hij hex
        have hlabel : u.val.symm cCell=j := by
          apply u.val.injective
          rw [Equiv.apply_symm_apply]
          change cCell=(exchange t i j hij hex).val j
          rw [exchange_apply,Equiv.swap_apply_right]
          exact he.symm
        have hdist : n-(u.val.symm cCell).val < d := by
          rw [hlabel]
          change n-(i.val+1) < d
          omega
        obtain ⟨w,hw,hc'⟩ := ih _ hdist u rfl
        have htu : FillingReachable t u := Relation.ReflTransGen.single ⟨i,j,hij,hex,rfl⟩
        exact ⟨w,htu.trans hw,hc'⟩
  exact aux _ t rfl

end
end Paper20.YoungShapes
