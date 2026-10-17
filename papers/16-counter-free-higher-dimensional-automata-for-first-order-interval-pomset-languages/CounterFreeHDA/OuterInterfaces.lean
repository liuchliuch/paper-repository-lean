import CounterFreeHDA.GluingDeletion

namespace CounterFreeHDA
universe u
variable {Lab : Type u} {A B P : PomsetData Lab}

/-- New ordered outside interfaces selected from the two original outside
interfaces; the common gluing interface is retained exactly. -/
structure OuterSelection (A B : PomsetData Lab) where
  sourceLen : ℕ
  targetLen : ℕ
  source : Fin sourceLen → Fin A.n
  target : Fin targetLen → Fin B.n
  source_inj : Function.Injective source
  target_inj : Function.Injective target
  source_mem : ∀ i, A.inSrc (source i)
  target_mem : ∀ i, B.inTgt (target i)
  source_order : ∀ i j, A.eord (source i) (source j) ↔ i < j
  target_order : ∀ i j, B.eord (target i) (target j) ↔ i < j

namespace OuterSelection
variable (E : OuterSelection A B)

def leftData : PomsetData Lab := { A with srcLen := E.sourceLen,src := E.source,src_inj := E.source_inj }
def rightData : PomsetData Lab := { B with tgtLen := E.targetLen,tgt := E.target,tgt_inj := E.target_inj }

theorem left_wf (hA : IsIntervalPom A) : IsIntervalPom E.leftData := { hA with
  src_minimal := by
    rintro e ⟨i,rfl⟩ f
    exact hA.src_minimal _ (E.source_mem i) f
  src_eord := E.source_order }

theorem right_wf (hB : IsIntervalPom B) : IsIntervalPom E.rightData := { hB with
  tgt_maximal := by
    rintro e ⟨i,rfl⟩ f
    exact hB.tgt_maximal _ (E.target_mem i) f
  tgt_eord := E.target_order }

variable {m : GlueMatch A B} (R : GluingRealization m P)

def globalData : PomsetData Lab := { P with
  srcLen := E.sourceLen,tgtLen := E.targetLen
  src := R.left ∘ E.source,tgt := R.right ∘ E.target
  src_inj := R.left.injective.comp E.source_inj
  tgt_inj := R.right.injective.comp E.target_inj }

theorem global_wf (hP : IsIntervalPom P) : IsIntervalPom (E.globalData R) := { hP with
  src_minimal := by
    rintro e ⟨i,rfl⟩ f
    obtain ⟨j,hj⟩ := E.source_mem i
    have hm : P.inSrc (R.left (E.source i)) :=
      ⟨Fin.cast R.source_len j,(R.source j).symm.trans (congrArg R.left hj)⟩
    exact hP.src_minimal _ hm f
  tgt_maximal := by
    rintro e ⟨i,rfl⟩ f
    obtain ⟨j,hj⟩ := E.target_mem i
    have hm : P.inTgt (R.right (E.target i)) :=
      ⟨Fin.cast R.target_len j,(R.target j).symm.trans (congrArg R.right hj)⟩
    exact hP.tgt_maximal _ hm f
  src_eord := fun i j => (R.left_eord _ _).trans (E.source_order i j)
  tgt_eord := fun i j => (R.right_eord _ _).trans (E.target_order i j) }

def matching : GlueMatch E.leftData E.rightData where
  len_eq := m.len_eq
  lab_eq := m.lab_eq

def realization : GluingRealization (E.matching (m := m)) (E.globalData R) where
  left := R.left
  right := R.right
  left_lab := R.left_lab
  right_lab := R.right_lab
  left_prec := R.left_prec
  right_prec := R.right_prec
  left_eord := R.left_eord
  right_eord := R.right_eord
  seam := R.seam
  overlap := R.overlap
  cover := R.cover
  cross := R.cross
  source_len := rfl
  target_len := rfl
  source _ := rfl
  target _ := rfl

/-- Changing only the two outside interfaces commutes with actual gluing,
without adding events or precedence relations to either factor. -/
noncomputable def iso (hA : IsIntervalPom A) (hB : IsIntervalPom B) (hP : IsIntervalPom P) :
    PomsetIso (glueData E.leftData E.rightData (E.matching (m := m))) (E.globalData R) :=
  (E.realization R).iso (E.left_wf hA) (E.right_wf hB) (E.global_wf R hP)

end OuterSelection
end CounterFreeHDA
