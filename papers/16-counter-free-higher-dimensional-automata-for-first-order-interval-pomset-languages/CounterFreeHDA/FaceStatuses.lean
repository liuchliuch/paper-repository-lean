import CounterFreeHDA.CornerIsomorphism

namespace CounterFreeHDA.Cubical.Face
universe u
variable {Lab : Type u} {k : ℕ}

noncomputable def activeIndices (U : Cube Lab k) (σ : Fin U.dim → Status) : Finset (Fin U.dim) :=
  Finset.univ.filter (fun i => σ i = Status.star)

noncomputable def activeCube (U : Cube Lab k) (σ : Fin U.dim → Status) : Cube Lab k := by
  have hc : (activeIndices U σ).card ≤ U.dim := by
    simpa only [Finset.card_univ,Fintype.card_fin] using Finset.card_le_card (Finset.filter_subset (fun i => σ i = Status.star) Finset.univ)
  exact ⟨⟨(activeIndices U σ).card,by have hu := U.1.isLt; change U.dim < k+1 at hu; omega⟩,
    fun i => U.lab ((activeIndices U σ).orderEmbOfFin rfl i)⟩

noncomputable def statusCell (U : Cube Lab k) (σ : Fin U.dim → Status) :
    TrackCell (Arrow.ident U).pom.val (activeCube U σ) where
  status := σ
  config _ _ h _ := False.elim h
  occ := (activeIndices U σ).orderEmbOfFin rfl
  inj := (activeIndices U σ).orderEmbOfFin rfl |>.injective
  active i := (Finset.mem_filter.mp ((activeIndices U σ).orderEmbOfFin_mem rfl i)).2
  covers e he := by
    have hm : e ∈ activeIndices U σ := Finset.mem_filter.mpr ⟨Finset.mem_univ e,he⟩
    let i := (activeIndices U σ).orderIsoOfFin rfl |>.symm ⟨e,hm⟩
    exact ⟨i,congrArg Subtype.val ((activeIndices U σ).orderIsoOfFin rfl |>.apply_symm_apply ⟨e,hm⟩)⟩
  labels _ := rfl
  ordered _ _ := (activeIndices U σ).orderEmbOfFin rfl |>.strictMono.lt_iff_lt

/-- Every full 0/star/1 assignment, including mixed lower/upper constants,
is an actual labelled face of U. -/
noncomputable def ofStatuses (U : Cube Lab k) (σ : Fin U.dim → Status) : Face (activeCube U σ) U :=
  TrackCell.faceFrom (statusCell U σ) (Arrow.ident U).sourceCell
    (fun e he => False.elim (he (Arrow.identity_full U e)))

@[simp] theorem ofStatuses_status (U : Cube Lab k) (σ : Fin U.dim → Status) (i : Fin U.dim) :
    (ofStatuses U σ).status i = σ i := by
  have hf := TrackCell.faceFrom_face (statusCell U σ) (Arrow.ident U).sourceCell
    (fun e he => False.elim (he (Arrow.identity_full U e)))
  have hs := TrackCell.face_status_occ (ofStatuses U σ) (Arrow.ident U).sourceCell i
  exact hs.symm.trans (congrArg (fun c : TrackCell (Arrow.ident U).pom.val (activeCube U σ) => c.status i) hf)

end CounterFreeHDA.Cubical.Face
