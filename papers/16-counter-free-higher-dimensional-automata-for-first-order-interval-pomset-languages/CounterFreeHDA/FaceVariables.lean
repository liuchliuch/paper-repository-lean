import CounterFreeHDA.CornerEmbedding

namespace CounterFreeHDA.Cubical.Face
universe u
variable {Lab : Type u} {k : ℕ} {U V : Cube Lab k}

noncomputable def activePositions (f : Face U V) : Finset (Fin V.dim) := by
  classical
  exact Finset.univ.filter (fun j => f.status j = Status.star)

theorem status_star_iff (f : Face U V) (j : Fin V.dim) :
    f.status j = Status.star ↔ ∃ i, f.position i = j := by
  constructor
  · intro hj
    cases hs : f.sub j with
    | inl i => exact ⟨i,(f.position_unique hs).symm⟩
    | inr b =>
      cases b <;> simp only [Face.status,hs] at hj <;>
        have hv := congrArg Fin.val hj <;> norm_num at hv
  · rintro ⟨i,rfl⟩
    simp only [Face.status,f.position_spec]

theorem activePositions_eq_image (f : Face U V) :
    f.activePositions = Finset.univ.image f.position := by
  classical
  ext j
  simp only [activePositions,Finset.mem_filter,Finset.mem_univ,true_and,
    Finset.mem_image,f.status_star_iff]

theorem activePositions_card (f : Face U V) : f.activePositions.card = U.dim := by
  classical
  rw [activePositions_eq_image,Finset.card_image_of_injective _ f.position_injective,
    Finset.card_univ,Fintype.card_fin]

theorem position_orderEmb (f : Face U V) :
    f.position = f.activePositions.orderEmbOfFin f.activePositions_card := by
  classical
  apply Finset.orderEmbOfFin_unique
  · intro i
    simp only [activePositions,Finset.mem_filter,Finset.mem_univ,true_and]
    exact (f.status_star_iff _).mpr ⟨i,rfl⟩
  · exact f.position_strictMono

theorem activePositions_orderEmb (f : Face U V) (i : Fin f.activePositions.card) :
    f.activePositions.orderEmbOfFin rfl i = f.position (Fin.cast f.activePositions_card i) := by
  rw [f.position_orderEmb]
  apply (Finset.orderEmbOfFin_eq_orderEmbOfFin_iff).mpr
  rfl

end CounterFreeHDA.Cubical.Face
