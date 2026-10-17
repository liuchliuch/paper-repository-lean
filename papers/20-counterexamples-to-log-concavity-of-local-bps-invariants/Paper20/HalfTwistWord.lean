import Paper20.BraidWalk

namespace Paper20.HalfTwistWord
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

def word : ℕ → List ℕ
  | 0 => []
  | n+1 => word n++(List.range (n+1)).reverse

lemma mem_word (n j : ℕ) (hj : j ∈ word n) : j < n := by
  induction n with
  | zero => simp [word] at hj
  | succ n ih =>
    rw [word,List.mem_append] at hj
    rcases hj with hj | hj
    · exact Nat.lt_trans (ih hj) (Nat.lt_succ_self n)
    · simpa only [List.mem_reverse,List.mem_range] using hj

lemma descending_ofFn (n : ℕ) :
    List.ofFn (fun i : Fin n => i.rev.val)=(List.range n).reverse := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp only [List.getElem_ofFn,Fin.val_rev,List.getElem_reverse,List.length_range,
      List.getElem_range]
    omega

/-- The standard executable half-twist word is the same triangular word
in natural generator indices. -/
theorem deltaWord_values (n : ℕ) :
    (BraidWalk.deltaWord n).map Fin.val=word n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [BraidWalk.deltaWord,List.map_append,List.map_map,List.map_ofFn]
    have he : ((BraidWalk.deltaWord n).map
        (fun i => (Fin.castSucc i).val))=(BraidWalk.deltaWord n).map Fin.val := rfl
    dsimp only [Function.comp_def]
    rw [he,ih,descending_ofFn,word]

section Monoid
variable {M : Type*} [Monoid M]

def down (g : ℕ → M) (n : ℕ) : M := ((List.range n).reverse.map g).prod
def up (g : ℕ → M) (n : ℕ) : M := ((List.range n).map g).prod
def triangle (g : ℕ → M) (n : ℕ) : M := ((word n).map g).prod

lemma down_succ (g : ℕ → M) (n : ℕ) : down g (n+1)=g n*down g n := by
  simp [down,List.range_succ]

lemma up_succ (g : ℕ → M) (n : ℕ) : up g (n+1)=up g n*g n := by
  simp [up,List.range_succ]

lemma triangle_succ (g : ℕ → M) (n : ℕ) :
    triangle g (n+1)=triangle g n*down g (n+1) := by
  simp only [triangle,word,List.map_append,List.prod_append,down]

lemma triangle_commute (g : ℕ → M) (n m : ℕ)
    (h : ∀ j, j < n → Commute (g j) (g m)) : Commute (triangle g n) (g m) := by
  apply Commute.list_prod_left
  intro a ha
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ha
  exact h j (mem_word n j hj)

/-- The two triangular expressions for the half twist agree using only
commutation of distant generators. This is the explicit reversal needed
for the source's palindromic full-twist argument. -/
theorem triangle_mirror (g : ℕ → M)
    (hfar : ∀ i j, i+1 < j → Commute (g i) (g j)) (n : ℕ) :
    triangle g (n+1)=up g (n+1)*triangle g n := by
  induction n with
  | zero => simp [triangle,word,up]
  | succ n ih =>
    have hc := triangle_commute g n (n+1) (fun j hj => hfar j (n+1) (by omega))
    calc
      triangle g (n+2) = triangle g (n+1)*(g (n+1)*down g (n+1)) := by
        rw [triangle_succ,down_succ]
      _ = (up g (n+1)*g (n+1))*(triangle g n*down g (n+1)) := by
        rw [ih]
        simpa only [mul_assoc] using congrArg
          (fun x => up g (n+1)*x*down g (n+1)) hc.eq
      _ = up g (n+2)*triangle g (n+1) := by
        rw [up_succ g (n+1),triangle_succ g n]

end Monoid
end
end Paper20.HalfTwistWord
