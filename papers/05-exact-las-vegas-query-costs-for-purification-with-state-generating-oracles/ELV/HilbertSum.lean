import ELV.UnitaryExtension

noncomputable section
namespace ELV.Stabilize
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F G E' F' : Type*}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E']
  [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F']

/-- Orthogonal direct sum of two unitary equivalences. -/
def pairCongr (e : E ≃ₗᵢ[𝕜] E') (f : F ≃ₗᵢ[𝕜] F') :
    HilbertPair E F ≃ₗᵢ[𝕜] HilbertPair E' F' where
  toLinearEquiv := (WithLp.linearEquiv 2 𝕜 (E × F)).trans
    ((e.toLinearEquiv.prodCongr f.toLinearEquiv).trans
      (WithLp.linearEquiv 2 𝕜 (E' × F')).symm)
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [WithLp.prod_norm_sq_eq_of_L2]

@[simp] lemma pairCongr_apply (e : E ≃ₗᵢ[𝕜] E') (f : F ≃ₗᵢ[𝕜] F') (x : E) (y : F) :
    pairCongr e f (WithLp.toLp 2 (x,y)) = WithLp.toLp 2 (e x, f y) := rfl

/-- Associativity of the Hilbert direct sum. -/
def pairAssoc : HilbertPair (HilbertPair E F) G ≃ₗᵢ[𝕜] HilbertPair E (HilbertPair F G) where
  toLinearEquiv :=
    { toFun := fun z => WithLp.toLp 2 (z.fst.fst, WithLp.toLp 2 (z.fst.snd, z.snd))
      invFun := fun z => WithLp.toLp 2 (WithLp.toLp 2 (z.fst, z.snd.fst), z.snd.snd)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [WithLp.prod_norm_sq_eq_of_L2]
    change ‖x.fst.fst‖ ^ 2 + (‖x.fst.snd‖ ^ 2 + ‖x.snd‖ ^ 2) =
      (‖x.fst.fst‖ ^ 2 + ‖x.fst.snd‖ ^ 2) + ‖x.snd‖ ^ 2
    ring

/-- Reorder `H ⊕ (Q ⊕ A)` into `(H ⊕ A) ⊕ Q`, so that only `Q` is queried. -/
def queryLayout : HilbertPair E (HilbertPair F G) ≃ₗᵢ[𝕜] HilbertPair (HilbertPair E G) F where
  toLinearEquiv :=
    { toFun := fun z => WithLp.toLp 2 (WithLp.toLp 2 (z.fst, z.snd.snd), z.snd.fst)
      invFun := fun z => WithLp.toLp 2 (z.fst.fst, WithLp.toLp 2 (z.snd, z.fst.snd))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [WithLp.prod_norm_sq_eq_of_L2]
    change (‖x.fst‖ ^ 2 + ‖x.snd.snd‖ ^ 2) + ‖x.snd.fst‖ ^ 2 =
      ‖x.fst‖ ^ 2 + (‖x.snd.fst‖ ^ 2 + ‖x.snd.snd‖ ^ 2)
    ring

variable [CompleteSpace E]

/-- Orthogonal decomposition as a unitary, for every closed subspace. -/
def orthogonalSplit (K : Submodule 𝕜 E) [CompleteSpace K] :
    E ≃ₗᵢ[𝕜] HilbertPair K Kᗮ where
  toLinearEquiv :=
    { toFun := fun x => WithLp.toLp 2 (K.orthogonalProjection x, Kᗮ.orthogonalProjection x)
      invFun := fun z => (z.fst : E) + (z.snd : E)
      left_inv := projection_sum K
      right_inv := by
        intro z
        apply (WithLp.equiv 2 (K × Kᗮ)).injective
        apply Prod.ext <;> simp [proj_K_of_mem, proj_K_of_mem_orthogonal,
          proj_Korth_of_mem_K, proj_Korth_of_mem]
      map_add' := by intros; simp [map_add]; rfl
      map_smul' := by intros; simp [map_smul]; rfl }
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [WithLp.prod_norm_sq_eq_of_L2]
    exact (proj_norm_sq (K := K) x).symm

@[simp] lemma orthogonalSplit_zero (K : Submodule 𝕜 E) [CompleteSpace K] :
    orthogonalSplit K 0 = 0 := map_zero _

section Embed
variable [CompleteSpace F]
variable (J : Submodule 𝕜 F) [CompleteSpace J] (e : E ≃ₗᵢ[𝕜] J)

/-- Split the added space into a second ambient copy and an unused part. -/
def embeddingSplit : HilbertPair E F ≃ₗᵢ[𝕜] HilbertPair (HilbertPair E E) Jᗮ :=
  ((pairCongr (LinearIsometryEquiv.refl 𝕜 E)
    ((orthogonalSplit J).trans
      (pairCongr e.symm (LinearIsometryEquiv.refl 𝕜 Jᗮ)))).trans
        (pairAssoc (𝕜 := 𝕜) (E := E) (F := E) (G := Jᗮ)).symm)

@[simp] lemma embeddingSplit_apply_zero (x : E) :
    embeddingSplit J e (WithLp.toLp 2 (x, (0 : F))) =
      WithLp.toLp 2 (WithLp.toLp 2 (x, (0 : E)), (0 : Jᗮ)) := by
  simp [embeddingSplit, pairAssoc, pairCongr, orthogonalSplit]
  rfl

/-- Extend a unitary on two ambient copies to an arbitrary added space
containing an isometric copy of the ambient Hilbert space. -/
def extendDouble (U : HilbertPair E E ≃ₗᵢ[𝕜] HilbertPair E E) :
    HilbertPair E F ≃ₗᵢ[𝕜] HilbertPair E F :=
  (embeddingSplit J e).trans
    ((pairCongr U (LinearIsometryEquiv.refl 𝕜 Jᗮ)).trans (embeddingSplit J e).symm)

lemma extendDouble_apply (U : HilbertPair E E ≃ₗᵢ[𝕜] HilbertPair E E)
    (x y : E) (h : U (WithLp.toLp 2 (x, (0 : E))) = WithLp.toLp 2 (y, (0 : E))) :
    extendDouble J e U (WithLp.toLp 2 (x, (0 : F))) = WithLp.toLp 2 (y, (0 : F)) := by
  apply (embeddingSplit J e).injective
  simp [extendDouble, LinearIsometryEquiv.trans_apply, embeddingSplit_apply_zero, h]

end Embed
end ELV.Stabilize
