import CounterFreeHDA.SourceExpansion
import CounterFreeHDA.TerminatorGlue
import CounterFreeHDA.FullIdentity

namespace CounterFreeHDA.Cubical
universe u
variable {Lab : Type u} {k : ℕ}

namespace Cube

theorem interface_injective : Function.Injective (cubeInterface (Lab := Lab) (k := k)) := by
  rintro ⟨n,lu⟩ ⟨m,lv⟩ h
  have hn : n = m := Fin.ext (congrArg Sigma.fst h)
  subst m
  have hl : lu = lv := by
    simpa only [cubeInterface,Cube.dim,Cube.lab,Sigma.mk.inj_iff,heq_eq_eq,true_and] using h
  subst lv
  rfl

end Cube

/-- Existence of a real elementary ST word, with its actual glued label. -/
def STRepresented (P : PomsetData Lab) : Prop :=
  ∃ (U V : Cube Lab k) (p : Word U V), Nonempty (PomsetIso p.label.pom.val P)

namespace STRepresented

theorem typed {U V : Cube Lab k} (A : Arrow U V) (h : STRepresented (k := k) A.pom.val) :
    ∃ p : Word U V, Nonempty (PomsetIso p.label.pom.val A.pom.val) := by
  obtain ⟨U',V',p,⟨φ⟩⟩ := h
  have hu : U' = U := Cube.interface_injective
    ((p.label.source.symm.trans φ.source_type).trans A.source)
  have hv : V' = V := Cube.interface_injective
    ((p.label.target.symm.trans φ.target_type).trans A.target)
  subst U'
  subst V'
  exact ⟨p,⟨φ⟩⟩

theorem of_iso {P Q : PomsetData Lab} (h : STRepresented (k := k) P) (φ : PomsetIso P Q) :
    STRepresented (k := k) Q := by
  obtain ⟨U,V,p,⟨ψ⟩⟩ := h
  exact ⟨U,V,p,⟨ψ.trans φ⟩⟩

theorem identity (U : Cube Lab k) : STRepresented (k := k) (Arrow.ident U).pom.val :=
  ⟨U,U,.nil U,⟨PomsetIso.refl _⟩⟩

theorem full {P : PomsetData Lab} (hP : IsIntervalPom P) (hw : P.WidthLE k)
    (hfull : ∀ e, P.inSrc e ∧ P.inTgt e) : STRepresented (k := k) P := by
  let U := sourceCube P (hw.source_bound hP)
  have hi : STRepresented (k := k) (identityPom Lab P.srcLen (P.lab ∘ P.src)).val := identity U
  exact hi.of_iso (FullIdentity.iso P hP (fun e => (hfull e).1) (fun e => (hfull e).2)).symm

end STRepresented

/-- Finite residual measure: one unit for each start or stop not already
accounted for by the two distinguished interfaces. -/
def stMeasure (P : PomsetData Lab) : ℕ := 2 * P.n - P.srcLen - P.tgtLen

structure PeelFactor (P : PomsetData Lab) where
  sourceType : Cube Lab k
  targetType : Cube Lab k
  middleType : Cube Lab k
  step : Step sourceType middleType
  tail : Arrow middleType targetType
  iso : PomsetIso (step.label.comp tail).pom.val P
  width : tail.pom.val.WidthLE k
  decreases : stMeasure tail.pom.val < stMeasure P

namespace PeelFactor

theorem represented {P : PomsetData Lab} (F : PeelFactor (k := k) P)
    (h : STRepresented (k := k) F.tail.pom.val) : STRepresented (k := k) P := by
  obtain ⟨p,⟨φ⟩⟩ := h.typed F.tail
  let m := GlueMatch.ofType (F.step.label.target.trans p.label.source.symm)
  let m' := GlueMatch.ofType (F.step.label.target.trans F.tail.source.symm)
  have hi := PomsetIso.glueIso (PomsetIso.refl F.step.label.pom.val) φ m m'
  exact ⟨F.sourceType,F.targetType,.cons F.step p,⟨hi.trans F.iso⟩⟩

end PeelFactor
end CounterFreeHDA.Cubical
