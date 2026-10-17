import Paper19.Main

open Paper19 Paper19.Spec Paper19.Infinitary
namespace Paper19.Challenge

theorem lemma_2_path_conversions : Lemma2_PathConversions := by
  intro T
  exact ⟨fun f hf => path_to_STree hf, fun g hg => path_from_STree hg⟩

theorem lemma_2_normal_form : Lemma2_NormalForm := by
  intro T hT
  exact ⟨STree_computable T hT, lemma2_ext_primrec T⟩

theorem lemma_2_finite_basis : Lemma2_UrhoBasis := by
  intro T n ρ
  exact Urho_basis T ρ

theorem lemma_3_rank_bound : Lemma3_RankBound := by
  intro T hT n
  exact lemma3_KB_bound T hT n

theorem lemma_4_iso_char : Lemma4_IsoChar := by
  intro T f
  exact ⟨f.toValidIso, f.translation_action⟩

theorem lemma_4_iso_converse : Lemma4_IsoConverse := by
  intro T c
  exact ⟨validIsoToPresentation c, fun _ => rfl⟩

theorem lemma_4_aut_char : Lemma4_AutChar := by
  intro T tag f
  exact ⟨f.toValidAut, f.translation_action⟩

theorem lemma_4_aut_converse : Lemma4_AutConverse := by
  intro T tag c
  exact ⟨validAutToPresentation c tag, fun _ => rfl⟩

theorem lemma_4_hom_proj : Lemma4_HomProj := by
  intro T n F G hF hG
  exact proj_hom hF hG

theorem lemma_5_path_to_iso : Lemma5_PathToIso := by
  intro T f hf
  exact ⟨validIsoToPresentation (validIsoOfPath hf)⟩

theorem lemma_5_iso_to_path : Lemma5_IsoToPath := by
  intro T f
  exact isPath_of_coherent f.toValidIso.val f.toValidIso.property

theorem lemma_6_infinite_lift : Lemma6_InfiniteLift := by
  intro T n F
  exact ⟨hasInfiniteLiftG_of_subset_ext, lemma6_ext_of_infiniteLift⟩

theorem lemma_6_dead_rank : Lemma6_DeadRank := by
  intro T n F σ hF hσ hd
  exact lemma6_dead_rank hF hσ hd

theorem thm1_isomorphic : Thm1_Isomorphic := by
  exact theorem1_isomorphic

theorem thm1_orbit_definitions : Thm1_OrbitDefinitions := by
  intro T hT tag m a
  exact all_tuple_orbits hT tag m a

theorem thm1_programs_correct : Thm1_ProgramsCorrect := by
  intro T f
  exact presentationToPath_correct f

theorem cor7_injection_tree : Cor7_InjectionTree := by
  intro L C D
  exact Highness.injPath_iff_iso C D

theorem theorem_1_full : Theorem1Statement := theorem_1

theorem lemma_2_full : Lemma2Statement := lemma2_full

theorem lemma_5_uniform : Lemma5UniformStatement := lemma5_uniform

theorem uniform_construction : UniformConstructionStatement := uniform_construction_all_inputs

end Paper19.Challenge
