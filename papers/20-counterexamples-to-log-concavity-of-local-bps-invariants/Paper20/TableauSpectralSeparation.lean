import Paper20.YoungOuterContents

namespace Paper20.YoungShapes
open Paper20.YoungCorners
noncomputable section
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

/-- All genuine standard Young fillings at the actual size, retaining
their actual final Young diagrams. -/
abbrev AllFilling (n : ℕ) := Σ μ : Shape n, StandardFilling μ

def allContent {n : ℕ} (t : AllFilling n) (i : Fin n) : ℤ := fillingContent t.2 i

def previousAll {n : ℕ} (t : AllFilling (n+1)) : AllFilling n :=
  ⟨fillingPrevious t.2,fillingPrefix t.2⟩

def finalCell {n : ℕ} (t : AllFilling (n+1)) : ℕ × ℕ := (t.2.val (Fin.last n)).val

lemma previous_final_addable {n : ℕ} (t : AllFilling (n+1)) :
    Addable (previousAll t).1.val (finalCell t) :=
  erased_addable t.1.val (finalCell t) (filling_last_removable t.2)

lemma filling_final_cells {n : ℕ} (t : AllFilling (n+1)) :
    t.1.val.cells=Insert.insert (finalCell t) (previousAll t).1.val.cells := by
  exact (congrArg YoungDiagram.cells
    (insert_erase t.1.val (finalCell t) (filling_last_removable t.2))).symm

/-- The actual content sequence separates all genuine standard tableaux,
including tableaux with different final diagrams. Each next content fixes
the actual addable corner of its already determined preceding diagram. -/
theorem allContent_injective (n : ℕ) : Function.Injective (fun t : AllFilling n => allContent t) := by
  induction n with
  | zero =>
    intro t u he
    rcases t with ⟨μ,t⟩
    rcases u with ⟨ν,u⟩
    have hμ : μ=ν := Subsingleton.elim ..
    subst ν
    apply congrArg (fun s : StandardFilling μ => (⟨μ,s⟩:AllFilling 0))
    apply Subtype.ext
    apply Equiv.ext
    intro i
    exact Fin.elim0 i
  | succ n ih =>
    intro t u he
    have hp : previousAll t=previousAll u := by
      apply ih
      funext i
      exact congrFun he i.castSucc
    have hprev : (previousAll t).1.val=(previousAll u).1.val :=
      congrArg (fun s : AllFilling n => s.1.val) hp
    have hlast : cellContent (finalCell t)=cellContent (finalCell u) := congrFun he (Fin.last n)
    have hdu : Addable (previousAll t).1.val (finalCell u) := by
      rw [hprev]
      exact previous_final_addable u
    have hc : finalCell t=finalCell u := addable_content_injective (previousAll t).1.val _ _
      (previous_final_addable t) hdu hlast
    have hfinal : t.1.val=u.1.val := by
      apply YoungDiagram.ext
      rw [filling_final_cells t,filling_final_cells u,hprev,hc]
    have hshape : t.1=u.1 := Subtype.ext hfinal
    rcases t with ⟨μ,t⟩
    rcases u with ⟨ν,u⟩
    dsimp only at hshape
    subst ν
    apply congrArg (fun s : StandardFilling μ => (⟨μ,s⟩:AllFilling (n+1)))
    apply Subtype.ext
    apply Equiv.ext
    intro i
    apply Subtype.ext
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact hc
    · exact congrArg (fun s : AllFilling n => (s.2.val j).val) hp

/-- With a faithful quantum parameter, the joint Murphy eigenvalue
sequence separates all actual standard-tableau basis positions. -/
theorem allEigenvalues_injective {F : Type*} [Field F] (v : F)
    (hv : Function.Injective (fun d : ℤ => v^d)) (n : ℕ) :
    Function.Injective (fun t : AllFilling n => fun i => v^(2*allContent t i)) := by
  intro t u he
  apply allContent_injective n
  funext i
  have h := hv (congrFun he i)
  dsimp only at h ⊢
  omega

end
end Paper20.YoungShapes
