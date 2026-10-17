import CounterFreeHDA.EventIsomorphism

namespace CounterFreeHDA.Cubical.BoundedArrow
universe u
variable {Lab : Type u} {k : ℕ} {U V W : Cube Lab k}

noncomputable def compIso {A A' : BoundedArrow U V} {B B' : BoundedArrow V W}
    (φ : PomsetIso A.pom.val A'.pom.val) (ψ : PomsetIso B.pom.val B'.pom.val) :
    PomsetIso (A.comp B).pom.val (A'.comp B').pom.val :=
  PomsetIso.glueIso φ ψ (GlueMatch.ofType (A.target.trans B.source.symm))
    (GlueMatch.ofType (A'.target.trans B'.source.symm))

end CounterFreeHDA.Cubical.BoundedArrow

namespace CounterFreeHDA.EndoPom
universe u
open Cubical
variable {Lab : Type u} {k : ℕ} {U : Cube Lab k}

noncomputable def bounded (P : EndoPom (cubeInterface U)) (hw : P.pom.val.WidthLE k) : BoundedArrow U U where
  pom := P.pom
  source := P.source
  target := P.target
  width := hw

theorem width_pow (P : EndoPom (cubeInterface U)) (hw : P.pom.val.WidthLE k) (n : ℕ) :
    (P.pow n).pom.val.WidthLE k := by
  induction n with
  | zero => exact PomsetData.widthLE_of_size_le _ (Nat.le_of_lt_succ U.1.isLt)
  | succ n ih => exact TrackGlue.width_glue _ (P.pow n).pom.property P.pom.property ih hw

noncomputable def boundedPower (P : EndoPom (cubeInterface U)) (hw : P.pom.val.WidthLE k) (n : ℕ) :
    BoundedArrow U U where
  pom := (P.pow n).pom
  source := (P.pow n).source
  target := (P.pow n).target
  width := P.width_pow hw n

@[simp] theorem boundedPower_zero (P : EndoPom (cubeInterface U)) (hw : P.pom.val.WidthLE k) :
    P.boundedPower hw 0 = BoundedArrow.ident U := rfl

@[simp] theorem boundedPower_succ (P : EndoPom (cubeInterface U)) (hw : P.pom.val.WidthLE k) (n : ℕ) :
    P.boundedPower hw (n+1) = (P.boundedPower hw n).comp (P.bounded hw) := rfl

/-- Actual powers split into two actual gluing powers up to pomset
isomorphism, including the zero-exponent identity factors. -/
noncomputable def powerAddIso (P : EndoPom (cubeInterface U)) (hw : P.pom.val.WidthLE k) (n m : ℕ) :
    PomsetIso ((P.boundedPower hw n).comp (P.boundedPower hw m)).pom.val (P.pow (n+m)).pom.val := by
  induction m with
  | zero => exact (P.boundedPower hw n).identityRightIso
  | succ m ih =>
    let A := P.boundedPower hw n
    let B := P.boundedPower hw m
    let C := P.bounded hw
    let D := P.boundedPower hw (n+m)
    have hp : PomsetIso ((A.comp B).comp C).pom.val (D.comp C).pom.val :=
      BoundedArrow.compIso ih (PomsetIso.refl _)
    exact (BoundedArrow.assocIso A B C).symm.trans hp

/-- The real three-block power decomposition used in Lemma 4.3. -/
noncomputable def powerBlockIso (P : EndoPom (cubeInterface U)) (hw : P.pom.val.WidthLE k)
    (n : ℕ) (hn : 2*k ≤ n) :
    PomsetIso (((P.boundedPower hw k).comp (P.boundedPower hw (n-2*k))).comp (P.boundedPower hw k)).pom.val
      (P.pow n).pom.val := by
  have he : k + (n-2*k) + k = n := by omega
  let A := P.boundedPower hw k
  let B := P.boundedPower hw (n-2*k)
  let C := P.boundedPower hw (k+(n-2*k))
  have hp : PomsetIso ((A.comp B).comp A).pom.val (C.comp A).pom.val :=
    BoundedArrow.compIso (P.powerAddIso hw k (n-2*k)) (PomsetIso.refl (P.pow k).pom.val)
  have hi := hp.trans (P.powerAddIso hw (k+(n-2*k)) k)
  simpa only [he] using hi

end CounterFreeHDA.EndoPom
