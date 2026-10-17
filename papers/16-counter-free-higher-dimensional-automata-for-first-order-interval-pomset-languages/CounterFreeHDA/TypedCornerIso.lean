import CounterFreeHDA.TypedCorners
import CounterFreeHDA.CornerIsomorphism

namespace CounterFreeHDA.Cubical.Arrow
universe u
variable {Lab : Type u} {k : ℕ} {U V T W : Cube Lab k}

/-- Corner isomorphism with the same actual typed faces at both ends. The
ordered interface equivalences preserve every position, even repeated labels. -/
noncomputable def cornerIso (A B : Arrow U V) (φ : PomsetIso A.pom.val B.pom.val)
    (hA : A.pom.val.WidthLE k) (hB : B.pom.val.WidthLE k)
    (α : Face T U) (β : Face W V) (ha : A.Compatible α β) (hb : B.Compatible α β) :
    PomsetIso (A.corner hA α β ha).pom.val (B.corner hB α β hb).pom.val := by
  have hs : (A.sourceFace α).status ∘ φ.srcEquiv.symm = (B.sourceFace α).status := by
    funext i
    apply congrArg α.status
    apply Fin.ext
    exact φ.symm.srcEquiv_val i
  have ht : (A.targetFace β).status ∘ φ.tgtEquiv.symm = (B.targetFace β).status := by
    funext i
    apply congrArg β.status
    apply Fin.ext
    exact φ.symm.tgtEquiv_val i
  have ψ := φ.cornerIso A.pom.property B.pom.property (A.sourceFace α).status
    (A.targetFace β).status (A.compatible_raw α β ha)
  change PomsetIso (Corners.data A.pom.val (A.sourceFace α).status (A.targetFace β).status (A.compatible_raw α β ha))
    (Corners.data B.pom.val (B.sourceFace α).status (B.targetFace β).status (B.compatible_raw α β hb))
  simpa only [hs,ht] using ψ

end CounterFreeHDA.Cubical.Arrow
