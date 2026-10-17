import CounterFreeHDA.CompletionCells
import CounterFreeHDA.AppendixCounterFree

namespace CounterFreeHDA.Appendix.Completion
open Cubical

def emptyCube : UCube := ⟨0,Fin.elim0⟩
def oneCube : UCube := ⟨1,fun _ => ()⟩

def endpointFace (b : Bool) : Cubical.Face emptyCube oneCube where
  sub _ := .inr b
  vars i := Fin.elim0 i
  ordered := by intro a c i j _ hi; cases hi
  labels := by intro a i hi; cases hi

theorem lowerFace : (endpointFace false).Lower := by
  intro j b hb
  exact (Sum.inr.inj hb).symm

theorem upperFace : (endpointFace true).Upper := by
  intro j b hb
  exact (Sum.inr.inj hb).symm

def letterWord : Word emptyCube emptyCube :=
  .cons (.start (endpointFace false) lowerFace rfl)
    (.cons (.stop (endpointFace true) upperFace rfl) (.nil emptyCube))

noncomputable def letter : EndoPom (cubeInterface emptyCube) where
  pom := letterWord.label.pom
  source := letterWord.label.source
  target := letterWord.label.target

theorem letter_width : letter.pom.val.WidthLE 2 := letterWord.label_width

def indexCell (U : UCube) (i : Fin (profileSize U.1)) : completionHDA.Cell U :=
  ⟨completionModel U i,⟨i,rfl⟩⟩

theorem indexCell_injective (U : UCube) : Function.Injective (indexCell U) :=
  fun _ _ h => completionModel_injective U (congrArg Subtype.val h)

theorem indexCell_surjective (U : UCube) : Function.Surjective (indexCell U) := by
  rintro ⟨x,i,rfl⟩
  exact ⟨i,rfl⟩

def letterRel : BRel 3 3 := fun i j => decide (∃ e : Fin 4,
  completionHDA.face (endpointFace false) (indexCell oneCube e) = indexCell emptyCube i ∧
  completionHDA.face (endpointFace true) (indexCell oneCube e) = indexCell emptyCube j)

theorem letterRel_eq : letterRel = residualA := by decide

theorem letterRun (i j : Fin 3) : letterRel i j = true ↔
    completionHDA.Run letterWord (indexCell emptyCube i) (indexCell emptyCube j) := by
  unfold letterWord
  rw [completionHDA.toPrecubical.run_start_iff]
  simp only [letterRel,decide_eq_true_eq]
  constructor
  · rintro ⟨e,hl,hu⟩
    refine ⟨indexCell oneCube e,hl.symm,?_⟩
    apply (completionHDA.toPrecubical.run_stop_iff _ _ _ _ _ _).mpr
    exact (completionHDA.toPrecubical.run_nil_iff _ _).mpr hu
  · rintro ⟨z,hz,hr⟩
    obtain ⟨e,rfl⟩ := indexCell_surjective oneCube z
    have hu := (completionHDA.toPrecubical.run_stop_iff _ _ _ _ _ _).mp hr
    exact ⟨e,hz.symm,(completionHDA.toPrecubical.run_nil_iff _ _).mp hu⟩

theorem letter_relation (i j : Fin 3) :
    indexCell emptyCube j ∈ completionHDA.toPrecubical.dPom (indexCell emptyCube i) letter.pom ↔ residualA i j = true := by
  change indexCell emptyCube j ∈ completionHDA.toPrecubical.dPom (indexCell emptyCube i) letterWord.label.pom ↔ _
  rw [completionHDA.toPrecubical.dPom_word,← letterRun,letterRel_eq]

theorem power_relation (n : ℕ) (i j : Fin 3) :
    indexCell emptyCube j ∈ completionHDA.toPrecubical.dPom (indexCell emptyCube i) (letter.pow n).pom ↔
      pow residualA n i j = true := by
  induction n generalizing i j with
  | zero =>
    change (indexCell emptyCube j ∈ completionHDA.toPrecubical.dPom (indexCell emptyCube i) (Word.nil emptyCube).label.pom) ↔ ident 3 i j = true
    rw [completionHDA.toPrecubical.dPom_word,completionHDA.toPrecubical.run_nil_iff]
    simp only [ident,decide_eq_true_eq]
    exact ⟨fun h => indexCell_injective emptyCube h,fun h => congrArg (indexCell emptyCube) h⟩
  | succ n ih =>
    have he := completionHDA.toPrecubical.dPom_comp (letter.boundedPower letter_width n) (letter.bounded letter_width)
      (indexCell emptyCube i) (indexCell emptyCube j)
    change (indexCell emptyCube j ∈ completionHDA.toPrecubical.dPom (indexCell emptyCube i)
      ((letter.boundedPower letter_width n).comp (letter.bounded letter_width)).pom) ↔ _
    rw [he]
    simp only [pow,comp,decide_eq_true_eq]
    constructor
    · rintro ⟨z,hz,hj⟩
      obtain ⟨l,rfl⟩ := indexCell_surjective emptyCube z
      exact ⟨l,(ih i l).mp hz,(letter_relation l j).mp hj⟩
    · rintro ⟨l,hl,hj⟩
      exact ⟨indexCell emptyCube l,(ih i l).mpr hl,(letter_relation l j).mpr hj⟩

/-- The ten-cell HDA of the displayed live completion has a genuine
period-two actual closed-letter relation and no counter-free exponent. -/
theorem completion_not_counterFreePom : ¬ completionHDA.toPrecubical.CounterFreePom := by
  rintro ⟨N,hN,H⟩
  apply residual_pow_ne_succ N hN
  funext i j
  apply Bool.eq_iff_iff.mpr
  exact (power_relation N i j).symm.trans
    (((congrArg (fun s => indexCell emptyCube j ∈ s) (H emptyCube (indexCell emptyCube i) letter)).to_iff).trans
      (power_relation (N+1) i j))

end CounterFreeHDA.Appendix.Completion
