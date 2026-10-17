import Paper19.UniformAllInputs

namespace Paper19

def Lemma2Statement : Prop :=
  UniformOracleComputable sProgram ∧
  UniformOracleComputable (fun o => pairStream (binaryOf o) (decodeBoundOf o)) ∧
  UniformOracleComputable (fun o => pathOfQT (streamBits o) (streamBounds o)) ∧
  ∀ T : InputTree, ComputablePred T.mem →
    ComputablePred (STree T.rootCompletion).mem ∧
    (∀ n, PrimrecPred (fun σ : Node => σ ∈ extLevel (STree T.rootCompletion) n)) ∧
    (∀ o, T.IsPath o →
      (STree T.rootCompletion).IsPath (pairStream (binaryOf o) (decodeBoundOf o))) ∧
    (∀ o, (STree T.rootCompletion).IsPath o →
      T.IsPath (pathOfQT (streamBits o) (streamBounds o))) ∧
    (∀ σ, sProgram (rootOracleProgram T.oracle) σ=true ↔ (STree T.rootCompletion).mem σ)

theorem lemma2_full : Lemma2Statement := by
  refine ⟨sProgram_uniform,pathCode_uniform,pathDecode_uniform,?_⟩
  intro T hT
  exact ⟨STree_computable _ (T.rootCompletion_computable hT),lemma2_ext_primrec _,
    fun o ho => path_to_STree ((T.path_iff_rootCompletion o).mp ho),
    fun o ho => (T.path_iff_rootCompletion _).mpr (path_from_STree ho),
    fun σ => by rw [rootOracle_correct]; exact sProgram_correct _ σ⟩

end Paper19
