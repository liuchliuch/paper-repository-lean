import CounterFreeHDA.TrackIso

/-! All elementary ST faces are obtained from increasing labelled embeddings
of interfaces, with the omitted position set to a lower or upper constant. -/
namespace CounterFreeHDA.Cubical.Face
universe u
variable {Lab : Type u} {k : ℕ} {U V : Cube Lab k}

noncomputable def ofEmbedding (a : Fin U.dim ↪o Fin V.dim)
    (hl : ∀ i, V.lab (a i) = U.lab i) (b : Bool) : Face U V := by
  classical
  let s : Fin V.dim → Fin U.dim ⊕ Bool := fun j =>
    if h : ∃ i, a i = j then Sum.inl (Classical.choose h) else Sum.inr b
  have hs : ∀ i, s (a i) = Sum.inl i := by
    intro i
    dsimp [s]
    rw [dif_pos ⟨i,rfl⟩]
    exact congrArg Sum.inl (a.injective (Classical.choose_spec (show ∃ j, a j = a i from ⟨i,rfl⟩)))
  have hinv : ∀ j i, s j = Sum.inl i → a i = j := by
    intro j i h
    dsimp [s] at h
    split_ifs at h with hj
    · have hji := Sum.inl.inj h
      rw [← hji]
      exact Classical.choose_spec hj
  exact {
    sub := s
    vars i := ⟨a i,hs i,fun j hj => (hinv j i hj).symm⟩
    ordered := by
      intro j j' i i' hj hsub hsub'
      rw [← hinv j i hsub,← hinv j' i' hsub'] at hj
      exact a.strictMono.lt_iff_lt.mp hj
    labels := by
      intro j i h
      rw [← hinv j i h]
      exact hl i }

@[simp] theorem ofEmbedding_position (a : Fin U.dim ↪o Fin V.dim)
    (hl : ∀ i, V.lab (a i) = U.lab i) (b : Bool) (i : Fin U.dim) :
    (ofEmbedding a hl b).position i = a i := by
  classical
  apply Eq.symm
  apply (ofEmbedding a hl b).position_unique
  change (if h : ∃ j, a j = a i then Sum.inl (Classical.choose h) else Sum.inr b) = Sum.inl i
  rw [dif_pos ⟨i,rfl⟩]
  exact congrArg Sum.inl (a.injective (Classical.choose_spec (show ∃ j, a j = a i from ⟨i,rfl⟩)))

@[simp] theorem ofEmbedding_positionEmbedding (a : Fin U.dim ↪o Fin V.dim)
    (hl : ∀ i, V.lab (a i) = U.lab i) (b : Bool) :
    (ofEmbedding a hl b).positionEmbedding = a := by
  ext i
  exact congrArg Fin.val (ofEmbedding_position a hl b i)

theorem ofEmbedding_constant (a : Fin U.dim ↪o Fin V.dim)
    (hl : ∀ i, V.lab (a i) = U.lab i) (b c : Bool) (j : Fin V.dim)
    (h : (ofEmbedding a hl b).sub j = Sum.inr c) : c = b := by
  classical
  change (if h : ∃ i, a i = j then Sum.inl (Classical.choose h) else Sum.inr b) = Sum.inr c at h
  split_ifs at h with hj
  exact (Sum.inr.inj h).symm

theorem ofEmbedding_lower (a : Fin U.dim ↪o Fin V.dim)
    (hl : ∀ i, V.lab (a i) = U.lab i) : (ofEmbedding a hl false).Lower := by
  intro j b h
  exact ofEmbedding_constant a hl false b j h

theorem ofEmbedding_upper (a : Fin U.dim ↪o Fin V.dim)
    (hl : ∀ i, V.lab (a i) = U.lab i) : (ofEmbedding a hl true).Upper := by
  intro j b h
  exact ofEmbedding_constant a hl true b j h

end CounterFreeHDA.Cubical.Face
