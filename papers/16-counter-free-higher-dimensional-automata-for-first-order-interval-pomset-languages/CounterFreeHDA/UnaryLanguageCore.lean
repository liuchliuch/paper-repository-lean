import CounterFreeHDA.ResidualWitnesses
import CounterFreeHDA.STLength

namespace CounterFreeHDA.Appendix.Residual
open Cubical Compare

def universalKind : (U : UCube) → Kind U
  | ⟨⟨0,_⟩,_⟩ => 2
  | ⟨⟨1,_⟩,_⟩ => 2
  | ⟨⟨2,_⟩,_⟩ => 1
  | ⟨⟨n+3,h⟩,_⟩ => False.elim (by omega)

attribute [local instance] Effective.faceFintype Effective.faceDecidableEq Effective.lowerDecidable Effective.upperDecidable

theorem universal_start : ∀ (U V : UCube) (f : Cubical.Face U V) (hl : f.Lower) (hd : V.dim = U.dim+1),
    startKind U.1 V.1 (universalKind U) = universalKind V := by
  let dec : Decidable (∀ (U V : UCube) (f : Cubical.Face U V) (hl : f.Lower) (hd : V.dim = U.dim+1),
      startKind U.1 V.1 (universalKind U) = universalKind V) := by
    refine @Fintype.decidableForallFintype _ _ (fun U => ?_) inferInstance
    refine @Fintype.decidableForallFintype _ _ (fun V => ?_) inferInstance
    refine @Fintype.decidableForallFintype _ _ (fun f => ?_) (Effective.faceFintype U V)
    infer_instance
  exact of_decide_eq_true (by rfl : @decide _ dec = true)

theorem universal_stop : ∀ (U V : UCube) (f : Cubical.Face U V) (hu : f.Upper) (hd : V.dim = U.dim+1),
    stopKind V.1 U.1 (universalKind V) = universalKind U := by
  let dec : Decidable (∀ (U V : UCube) (f : Cubical.Face U V) (hu : f.Upper) (hd : V.dim = U.dim+1),
      stopKind V.1 U.1 (universalKind V) = universalKind U) := by
    refine @Fintype.decidableForallFintype _ _ (fun U => ?_) inferInstance
    refine @Fintype.decidableForallFintype _ _ (fun V => ?_) inferInstance
    refine @Fintype.decidableForallFintype _ _ (fun f => ?_) (Effective.faceFintype U V)
    infer_instance
  exact of_decide_eq_true (by rfl : @decide _ dec = true)

theorem universal_word {U V : UCube} (p : Word U V) : wordKind p (universalKind U) = universalKind V := by
  induction p with
  | nil => rfl
  | cons s p ih =>
    cases s with
    | start f hl hd => simpa only [wordKind,stepKind,universal_start _ _ f hl hd] using ih
    | stop f hu hd => simpa only [wordKind,stepKind,universal_stop _ _ f hu hd] using ih

/-- From the second vertex every nonempty closed bounded pomset is
accepted; empty execution is the only excluded one. -/
theorem closed_word_B (p : Word Completion.emptyCube Completion.emptyCube) :
    acceptBit (wordKind p (1 : Fin 4)) = true ↔ 0 < p.length := by
  cases p with
  | nil => decide
  | @cons U V W s p =>
    have hs : stepKind s (1 : Fin 4) = universalKind V := by
      cases s with
      | start f hl hd =>
        rcases V with ⟨v,lab⟩
        have hv : v = 1 := Fin.ext (by simpa only [Cube.dim] using hd)
        subst v
        rfl
      | stop f hu hd => change 0 = V.dim+1 at hd; omega
    simp only [wordKind,hs,universal_word,Word.length]
    exact iff_of_true (by decide) (by omega)

theorem empty_interface_size (A : BoundedArrow Completion.emptyCube Completion.emptyCube)
    (p : Word Completion.emptyCube Completion.emptyCube) (φ : PomsetIso p.label.pom.val A.pom.val) :
    0 < p.length ↔ 0 < A.pom.n := by
  have hm := (p.stMeasure_label).symm.trans (stMeasure_iso φ)
  change p.length = 2*A.pom.n - A.pom.srcLen - A.pom.tgtLen at hm
  have hs := A.toArrow.src_len
  have ht := A.toArrow.tgt_len
  change A.pom.srcLen = 0 at hs
  change A.pom.tgtLen = 0 at ht
  rw [hs,ht] at hm
  omega

def NonemptyClosedLanguage : Set (Tail Completion.emptyCube) := {Q | 0 < Q.pom.n}

/-- B is exactly P+ in the paper, for actual suffix pomsets. -/
theorem residual_B : residualLanguage Completion.emptyCube (1 : Fin 4) = NonemptyClosedLanguage := by
  ext Q
  have hmem : Q ∈ residualLanguage Completion.emptyCube (1 : Fin 4) ↔
      acceptBit (wordKind Q.representative (1 : Fin 4)) = true := by
    rw [residualLanguage,suffix_mem_execute]
    simpa only [acceptBit,decide_eq_true_eq] using
      represents_acceptance _ _ (execute_represents Q.representative _ _ (representative_represents Completion.emptyCube (1 : Fin 4)))
  exact hmem.trans ((closed_word_B Q.representative).trans (empty_interface_size Q Q.representative Q.representativeIso))

/-- C0 accepts every closed bounded suffix, including the identity. -/
theorem residual_C0 : residualLanguage Completion.emptyCube (2 : Fin 4) = Set.univ := by
  ext Q
  rw [residualLanguage,suffix_mem_execute]
  have hh := represents_acceptance _ _ (execute_represents Q.representative _ _
    (representative_represents Completion.emptyCube (2 : Fin 4)))
  have hu : wordKind Q.representative (2 : Fin 4) = (2 : Fin 4) := universal_word Q.representative
  simp only [hu] at hh
  exact iff_of_true (hh.mpr (Or.inr trivial)) (Set.mem_univ Q)

end CounterFreeHDA.Appendix.Residual
