import CounterFreeHDA.EffectiveFaces
import CounterFreeHDA.STLength

namespace CounterFreeHDA.Cubical.Effective
universe u
variable {Lab : Type u} {k : ℕ} {U V : Cube Lab k}

def position (f : Face U V) (i : Fin U.dim) : Fin V.dim :=
  Finset.univ.choose (fun j => f.sub j = Sum.inl i) (by
    obtain ⟨j,hj,hu⟩ := f.vars i
    exact ⟨j,⟨Finset.mem_univ _,hj⟩,fun l hl => hu l hl.2⟩)

theorem position_eq (f : Face U V) (i : Fin U.dim) : position f i = f.position i  := by
  apply f.position_unique
  unfold position
  exact Finset.choose_property (fun j => f.sub j = Sum.inl i) Finset.univ _

def positionEmbedding (f : Face U V) : Fin U.dim ↪o Fin V.dim :=
  OrderEmbedding.ofStrictMono (position f) (by intro i j hij; simpa only [position_eq] using f.position_strictMono hij)

theorem positionEmbedding_eq (f : Face U V) : positionEmbedding f = f.positionEmbedding := by
  ext i
  exact congrArg Fin.val (position_eq f i)

def stepLabel : {U V : Cube Lab k} → Step U V → Arrow U V
  | _,_,.start f hl hd => {
    pom := discretePom _ (positionEmbedding f) (OrderEmbedding.ofStrictMono id (fun _ _ h => h))
    source := by
      refine Sigma.ext rfl ?_
      apply heq_of_eq
      funext i
      apply f.labels
      change f.sub (position f i) = Sum.inl i
      rw [position_eq]
      exact f.position_spec i
    target := rfl }
  | _,_,.stop f hu hd => {
    pom := discretePom _ (OrderEmbedding.ofStrictMono id (fun _ _ h => h)) (positionEmbedding f)
    source := rfl
    target := by
      refine Sigma.ext rfl ?_
      apply heq_of_eq
      funext i
      apply f.labels
      change f.sub (position f i) = Sum.inl i
      rw [position_eq]
      exact f.position_spec i }

theorem stepLabel_eq {U V : Cube Lab k} (s : Step U V) : stepLabel s = s.label := by
  cases s <;> simp only [stepLabel,Step.label,positionEmbedding_eq]

end CounterFreeHDA.Cubical.Effective
