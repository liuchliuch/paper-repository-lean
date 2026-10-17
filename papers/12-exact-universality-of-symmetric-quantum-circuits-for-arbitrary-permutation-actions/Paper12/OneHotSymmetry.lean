import Paper12.OneHotCircuit

noncomputable section
namespace Paper12
open Matrix Classical
variable {X : Type*} [Fintype X]

theorem Threshold.ext_data {J : Type*} {g h : Threshold J}
    (hh : g.head = h.head) (hc : g.controls = h.controls) (ht : g.threshold = h.threshold) : g = h := by
  cases g; cases h; simp_all

theorem flagEquality_map {J : Type*} [Fintype J] (e : J ≃ J) (S : Finset J) (t : ℕ)
    (hS : S.map e.toEmbedding = S) :
    (flagEquality S t).map (e.sumCongr (Equiv.refl (Fin 1))) = flagEquality S t := by
  apply Threshold.ext_data
  · rfl
  · change (S.map Function.Embedding.inl).map (e.sumCongr (Equiv.refl (Fin 1))).toEmbedding =
      S.map Function.Embedding.inl
    rw [Finset.map_map]
    have he : (Function.Embedding.inl : J ↪ J ⊕ Fin 1).trans
        (e.sumCongr (Equiv.refl (Fin 1))).toEmbedding = e.toEmbedding.trans Function.Embedding.inl := by
      ext x; rfl
    rw [he, ← Finset.map_map, hS]
  · rfl

theorem prepWeightTest_map (α : Coeffs X) (τ : SelectorWire α ≃ SelectorWire α) :
    (prepWeightTest α).map (τ.sumCongr (Equiv.refl (Fin 2))) = prepWeightTest α := by
  apply Threshold.ext_data
  · rfl
  · change ((Finset.univ : Finset (SelectorWire α)).map Function.Embedding.inl).map
      (τ.sumCongr (Equiv.refl (Fin 2))).toEmbedding = Finset.univ.map Function.Embedding.inl
    rw [Finset.map_map]
    have he : (Function.Embedding.inl : SelectorWire α ↪ SelectorWire α ⊕ Fin 2).trans
        (τ.sumCongr (Equiv.refl (Fin 2))).toEmbedding = τ.toEmbedding.trans Function.Embedding.inl := by
      ext x; rfl
    rw [he, ← Finset.map_map, Finset.map_univ_equiv]
  · rfl

theorem oneHotCircuit_preserved (α : Coeffs X) (τ : SelectorWire α ≃ SelectorWire α)
    (hα : ∀ q, α (τ q).val = α q.val) :
    (oneHotCircuit α).Preserved (liftFixW τ) := by
  let e := τ.sumCongr (Equiv.refl (Fin 2))
  have hd : ∀ q, selectorD α (τ q) = selectorD α q := by
    intro q
    unfold selectorD selectorAmp
    rw [hα q]
  have hT : (prepT α).Preserved e := by
    intro L hL
    simp only [prepT, parallelCircuit, List.mem_singleton] at hL
    subst L
    apply parallelLayer_map
    intro x
    cases x with
    | inl q => exact congrArg productRotation (hd q)
    | inr r => rfl
  have hTF := Circuit.preserved_onLeft (Equiv.refl (Fin 1)) hT
  have hD := equalityCircuit_preserved e (prepWeightTest α) (prepWeightTest_map α τ)
  have hDF := Circuit.preserved_onLeft (Equiv.refl (Fin 1)) hD
  have hS : ({Sum.inr 0, Sum.inr 1} : Finset (SelectorWire α ⊕ Fin 2)).map e.toEmbedding =
      {Sum.inr 0, Sum.inr 1} := by
    simp [e]
  have hFmid := equalityCircuit_preserved (e.sumCongr (Equiv.refl (Fin 1)))
    (flagEquality ({Sum.inr 0, Sum.inr 1} : Finset (SelectorWire α ⊕ Fin 2)) 2)
    (flagEquality_map e _ _ hS)
  have hFG : (prepFG α).Preserved (e.sumCongr (Equiv.refl (Fin 1))) :=
    Circuit.preserved_mul hDF (Circuit.preserved_mul hFmid hDF)
  have hF0 : (prepF0 α).Preserved (e.sumCongr (Equiv.refl (Fin 1))) :=
    equalityCircuit_preserved _ _ (flagEquality_map e _ _ (Finset.map_univ_equiv e))
  have hI : (prepIteration α).Preserved (e.sumCongr (Equiv.refl (Fin 1))) :=
    Circuit.preserved_mul hTF (Circuit.preserved_mul hF0
      (Circuit.preserved_mul (Circuit.preserved_adjoint hTF) hFG))
  have hZ (θ : ℝ) :
      ((singleCircuit (ryGate (0 : Fin 1) θ)).onRight (J := SelectorWire α ⊕ Fin 2)).Preserved
        (e.sumCongr (Equiv.refl (Fin 1))) :=
    Circuit.preserved_onRight e (singleCircuit_preserved (Equiv.refl (Fin 1)) _ rfl)
  have hR : ((singleCircuit (.one ⟨Sum.inr 1, pmat .X, pmat_unitary .X⟩ : Gate (SelectorWire α ⊕ Fin 2))).onLeft
      (K := Fin 1)).Preserved (e.sumCongr (Equiv.refl (Fin 1))) :=
    Circuit.preserved_onLeft _ (singleCircuit_preserved e _ rfl)
  have hRaw : (prepRaw α).Preserved (e.sumCongr (Equiv.refl (Fin 1))) :=
    Circuit.preserved_mul hR (Circuit.preserved_mul (hZ (Real.pi / 2))
      (Circuit.preserved_mul (Circuit.preserved_power hI 2)
        (Circuit.preserved_mul hTF (hZ (-Real.pi / 2)))))
  apply Circuit.preserved_rewire (prepWireEquiv α) hRaw
  intro x
  cases x with
  | inl x => cases x <;> rfl
  | inr x => rfl
end Paper12
