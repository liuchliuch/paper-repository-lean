import Paper25.SourcePreparationPlacement
import Paper25.HistoryCompilation

/-! Exact reflection about the complete small-register zero state in the same
physical/filter layout as the placed F. The h bit is used as the phase target,
so this construction also covers a zero-qubit catalyst without adding qubits. -/
noncomputable section
open Matrix
namespace Paper25.FullReflectionPlacement
open OperationalModel OperationalModel.LocalCompilation StatePreparation
open SourceCoordinates SourcePreparationPlacement
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1800000
set_option synthInstance.maxSize 512
variable {G : EffectiveGateSet}

abbrev AuxPos (m : ℕ) := Fin m ⊕ (Fin 1 ⊕ BPos)
abbrev OtherPos (S : EffectiveSourceComputation G) (ell m : ℕ) :=
  AuxPos m ⊕ (Fin ell ⊕ (WPos S ⊕ WPos S))
abbrev CatPos (S : EffectiveSourceComputation G) := CPos S ⊕ CPos S
abbrev ReflectionPos (S : EffectiveSourceComputation G) (ell m : ℕ) :=
  OtherPos S ell m ⊕ (Fin 1 ⊕ CatPos S)

def auxIntoUnused {S : EffectiveSourceComputation G} {m : ℕ} : AuxPos m → UnusedPos S m
  | .inl p => .inl p
  | .inr (.inl r) => .inr (.inl r)
  | .inr (.inr b) => .inr (.inr (.inl b))

def auxWire (m : ℕ) : AuxPos m ≃ Fin (m+(1+(1+3))) :=
  StatePreparationLocal.tensorWire (Equiv.refl _)
    (StatePreparationLocal.tensorWire (Equiv.refl _)
      (StatePreparationLocal.tensorWire (Equiv.refl _) (Equiv.refl _)))

def otherQubits (S : EffectiveSourceComputation G) (ell m : ℕ) : ℕ :=
  (m+(1+(1+3)))+(ell+((restQubits S+1)+(restQubits S+1)))

def otherWire (S : EffectiveSourceComputation G) (ell m : ℕ) :
    OtherPos S ell m ≃ Fin (otherQubits S ell m) :=
  StatePreparationLocal.tensorWire (auxWire m)
    (StatePreparationLocal.tensorWire (Equiv.refl _)
      (StatePreparationLocal.tensorWire (Equiv.refl _) (Equiv.refl _)))

def reflectionQubits (S : EffectiveSourceComputation G) (ell m : ℕ) : ℕ :=
  otherQubits S ell m + (S.catalystQubits+S.catalystQubits+1)

/-- Standard reflection order: all small bits except h, then h, then catalysts. -/
def nativePositionWire (S : EffectiveSourceComputation G) (ell m : ℕ) :
    ReflectionPos S ell m ≃ Fin (reflectionQubits S ell m) :=
  StatePreparationLocal.tensorWire (otherWire S ell m)
    (((Equiv.refl (Fin 1)).sumCongr finSumFinEquiv).trans
      (StatePreparationLocal.splitPosition (S.catalystQubits+S.catalystQubits)).symm)

def gatherReflection (S : EffectiveSourceComputation G) (ell m : ℕ) :
    ReflectionPos S ell m ≃ (FPos S ell ⊕ UnusedPos S m) where
  toFun p := match p with
    | .inl (.inl a) => .inr (auxIntoUnused a)
    | .inl (.inr (.inl c)) => .inl (.inr (.inl c))
    | .inl (.inr (.inr w)) => .inl (.inr (.inr (.inl w)))
    | .inr (.inl h) => .inl (.inl h)
    | .inr (.inr c) => .inr (.inr (.inr (.inr c)))
  invFun p := match p with
    | .inl (.inl h) => .inr (.inl h)
    | .inl (.inr (.inl c)) => .inl (.inr (.inl c))
    | .inl (.inr (.inr (.inl w))) => .inl (.inr (.inr w))
    | .inl (.inr (.inr (.inr a))) => Fin.elim0 a
    | .inr (.inl p) => .inl (.inl (.inl p))
    | .inr (.inr (.inl r)) => .inl (.inl (.inr (.inl r)))
    | .inr (.inr (.inr (.inl b))) => .inl (.inl (.inr (.inr b)))
    | .inr (.inr (.inr (.inr c))) => .inr (.inr c)
  left_inv p := by
    rcases p with (a | (c | w)) | (h | c)
    · rcases a with p | (r | b) <;> rfl
    all_goals rfl
  right_inv p := by
    rcases p with f | u
    · rcases f with h | (c | (w | a)) <;> first | rfl | exact Fin.elim0 a
    · rcases u with p | (r | (b | c)) <;> rfl

/-- This is a permutation of actual qubit positions, never a basis-state oracle. -/
def currentPositionWire (S : EffectiveSourceComputation G) (ell m : ℕ) :
    ReflectionPos S ell m ≃ Fin (filterQubits S ell m) :=
  (gatherReflection S ell m).trans (allPositions S ell m)

def reflectionWire (S : EffectiveSourceComputation G) (ell m : ℕ) :
    Fin (reflectionQubits S ell m) ≃ Fin (filterQubits S ell m) :=
  (nativePositionWire S ell m).symm.trans (currentPositionWire S ell m)

lemma reflectionWire_apply (S : EffectiveSourceComputation G) (ell m : ℕ)
    (p : ReflectionPos S ell m) :
    reflectionWire S ell m (nativePositionWire S ell m p) = currentPositionWire S ell m p := by
  exact congrArg (currentPositionWire S ell m) ((nativePositionWire S ell m).symm_apply_apply p)

def nativeIndex (S : EffectiveSourceComputation G) (ell m : ℕ) :
    Basis (filterQubits S ell m) ≃
      (Basis (otherQubits S ell m) × Basis (S.catalystQubits+S.catalystQubits+1)) :=
  (rewireBasis (reflectionWire S ell m)).trans
    (registerBasis (otherQubits S ell m) (S.catalystQubits+S.catalystQubits+1))

lemma prefix_read (S : EffectiveSourceComputation G) (ell m : ℕ)
    (x : Basis (filterQubits S ell m)) (p : OtherPos S ell m) :
    (nativeIndex S ell m x).1 (otherWire S ell m p) =
      x (currentPositionWire S ell m (.inl p)) := by
  change x (reflectionWire S ell m (nativePositionWire S ell m (.inl p))) = _
  exact congrArg x (reflectionWire_apply S ell m (.inl p))

lemma h_read (S : EffectiveSourceComputation G) (ell m : ℕ)
    (x : Basis (filterQubits S ell m)) :
    (nativeIndex S ell m x).2 0 = x (currentPositionWire S ell m (.inr (.inl 0))) := by
  change x (reflectionWire S ell m (nativePositionWire S ell m (.inr (.inl 0)))) = _
  exact congrArg x (reflectionWire_apply S ell m (.inr (.inl 0)))

lemma native_zero_iff (S : EffectiveSourceComputation G) (ell m : ℕ)
    (x : Basis (filterQubits S ell m)) :
    ((nativeIndex S ell m x).1 = (fun _ => 0) ∧ (nativeIndex S ell m x).2 0 = 0) ↔
      (∀ p : OtherPos S ell m, x (currentPositionWire S ell m (.inl p)) = 0) ∧
        x (currentPositionWire S ell m (.inr (.inl 0))) = 0 := by
  rw [h_read]
  constructor
  · rintro ⟨hp,hh⟩
    refine ⟨?_,hh⟩
    intro p
    rw [←prefix_read S ell m x p,hp]
  · rintro ⟨hp,hh⟩
    refine ⟨?_,hh⟩
    funext i
    have h := hp ((otherWire S ell m).symm i)
    rw [←prefix_read S ell m x ((otherWire S ell m).symm i),
      (otherWire S ell m).apply_symm_apply] at h
    exact h

lemma smallRead_zero (S : EffectiveSourceComputation G) (ell : ℕ) :
    smallRead S ell (smallZero ell (restQubits S) 0) = (fun _ => 0) := by
  funext j
  rw [smallRead_apply]
  rcases j with h | (c | ((w | w) | a))
  · rfl
  · rfl
  · change (splitBits (restQubits S)).symm (0,zeroBits (restQubits S)) w = 0
    rw [splitBits_symm_zero]
    rfl
  · change (splitBits (restQubits S)).symm (0,zeroBits (restQubits S)) w = 0
    rw [splitBits_symm_zero]
    rfl
  · exact Fin.elim0 a

lemma small_zero_iff (S : EffectiveSourceComputation G) (ell : ℕ)
    (x : Small ell (restQubits S) 0) :
    x = smallZero ell (restQubits S) 0 ↔
      ∀ f : FPos S ell, StatePreparationLocal.FRead ell (restQubits S) 0 x f = 0 := by
  rw [← (smallRead S ell).injective.eq_iff,smallRead_zero]
  constructor
  · intro h f; simpa only [smallRead_apply] using congrFun h f
  · intro h; funext f; simpa only [smallRead_apply] using h f

lemma aux_zero_iff (S : EffectiveSourceComputation G) (m : ℕ) (u : Untouched S m) :
    (unusedIndex S m u).1 = zeroBits (m+4+1) ↔
      ∀ a : AuxPos m, u (auxIntoUnused a) = 0 := by
  change packAux m ((fun i => u (.inl i)),
    (u (.inr (.inl 0)),(u (.inr (.inr (.inl (.inl 0)))),
      fun i => u (.inr (.inr (.inl (.inr i))))))) = zeroBits (m+4+1) ↔ _
  rw [Equiv.apply_eq_iff_eq_symm_apply]
  change ((fun i => u (.inl i)),
    (u (.inr (.inl 0)),(u (.inr (.inr (.inl (.inl 0)))),
      fun i => u (.inr (.inr (.inl (.inr i))))))) =
      (zeroBits m,(0,(0,zeroBits 3))) ↔ _
  constructor
  · intro h a
    rcases a with p | (r | (b | i))
    · exact congrFun (congrArg (fun p => p.1) h) p
    · fin_cases r
      exact congrArg (fun p => p.2.1) h
    · fin_cases b
      exact congrArg (fun p => p.2.2.1) h
    · exact congrFun (congrArg (fun p => p.2.2.2) h) i
  · intro h
    apply Prod.ext
    · funext i; exact h (.inl i)
    · apply Prod.ext
      · exact h (.inr (.inl 0))
      · apply Prod.ext
        · exact h (.inr (.inr (.inl 0)))
        · funext i; exact h (.inr (.inr (.inr i)))

lemma filter_zero_iff (S : EffectiveSourceComputation G) (ell m : ℕ)
    (x : Basis (filterQubits S ell m)) :
    (filterLayout S ell m x).1 = SourceSimulation.ancillaryZero ell (restQubits S) (m+4+1) ↔
      (∀ p : OtherPos S ell m, x (currentPositionWire S ell m (.inl p)) = 0) ∧
        x (currentPositionWire S ell m (.inr (.inl 0))) = 0 := by
  change ((unusedIndex S m (logicalLayout S ell m x).2).1,(logicalLayout S ell m x).1) =
      (zeroBits (m+4+1),smallZero ell (restQubits S) 0) ↔ _
  rw [Prod.mk.injEq,aux_zero_iff,small_zero_iff]
  constructor
  · rintro ⟨ha,hf⟩
    refine ⟨?_,?_⟩
    · intro p
      rcases p with a | (c | w)
      · exact ha a
      · simpa only [logicalLayout_selected] using hf (.inr (.inl c))
      · simpa only [logicalLayout_selected] using hf (.inr (.inr (.inl w)))
    · simpa only [logicalLayout_selected] using hf (.inl 0)
  · rintro ⟨hp,hh⟩
    constructor
    · intro a; exact hp (.inl a)
    · intro f
      rcases f with h | (c | (w | a))
      · fin_cases h; simpa only [logicalLayout_selected] using hh
      · simpa only [logicalLayout_selected] using hp (.inr (.inl c))
      · simpa only [logicalLayout_selected] using hp (.inr (.inr w))
      · exact Fin.elim0 a

def reflection (conv : GateConvention G) (S : EffectiveSourceComputation G) (ell m : ℕ) :
    EffectiveCircuit G (filterQubits S ell m) :=
  rewireCircuit (reflectionWire S ell m)
    (zeroSmallReflectionCircuit conv (otherQubits S ell m) (S.catalystQubits+S.catalystQubits))

/-- Exact reflection 2Π-1 about all small zero bits, with unrestricted catalysts.
The construction uses h as its target and is therefore valid also when c=0. -/
theorem reflection_matrix (conv : GateConvention G) (S : EffectiveSourceComputation G) (ell m : ℕ) :
    (reflection conv S ell m).matrix =
      (projectorReflection (OneCleanQubit.ancillaryProjector
        (n := SourceSimulation.CatalystData S.catalystQubits)
        (SourceSimulation.AuxiliarySmall ell (restQubits S) (m+4+1))
        (SourceSimulation.ancillaryZero ell (restQubits S) (m+4+1)))).submatrix
          (filterLayout S ell m) (filterLayout S ell m) := by
  rw [reflection,rewireCircuit_matrix,zeroSmallReflectionCircuit_matrix]
  ext x y
  have hz : (nativeIndex S ell m x).1 = (fun _ => 0) ∧ (nativeIndex S ell m x).2 0 = 0 ↔
      (filterLayout S ell m x).1 = SourceSimulation.ancillaryZero ell (restQubits S) (m+4+1) := by
    rw [native_zero_iff,filter_zero_iff]
  have he := (nativeIndex S ell m).injective.eq_iff (a := x) (b := y)
  have hf := (filterLayout S ell m).injective.eq_iff (a := x) (b := y)
  change (2 • (if nativeIndex S ell m x = nativeIndex S ell m y then
      (if (nativeIndex S ell m x).1 = (fun _ => 0) ∧ (nativeIndex S ell m x).2 0 = 0 then (1:ℂ) else 0)
      else 0) - (if nativeIndex S ell m x = nativeIndex S ell m y then 1 else 0)) = _
  simp only [he,hz,projectorReflection,OneCleanQubit.ancillaryProjector,
    Matrix.submatrix_apply,Matrix.sub_apply,Matrix.smul_apply,Matrix.diagonal_apply,Matrix.one_apply,hf]

theorem reflection_length (conv : GateConvention G) (S : EffectiveSourceComputation G) (ell m : ℕ) :
    (reflection conv S ell m).length ≤
      conv.bound^(otherQubits S ell m+1)*(5*conv.X.length+6*conv.bound)+
        4*(conv.X.length+conv.bound) := by
  rw [reflection,rewireCircuit_length]
  exact zeroSmallReflectionCircuit_length conv _ _

lemma otherQubits_add_one (S : EffectiveSourceComputation G) (ell m : ℕ) :
    otherQubits S ell m+1 = SourceSimulation.smallQubits ell (restQubits S) (m+4+1) := by
  unfold otherQubits SourceSimulation.smallQubits
  omega

lemma filterQubits_eq (S : EffectiveSourceComputation G) (ell m : ℕ) :
    filterQubits S ell m = SourceSimulation.smallQubits ell (restQubits S) (m+4+1) +
      S.catalystQubits+S.catalystQubits := by
  have h := restQubits_add_one S
  unfold filterQubits walkQubits encoderQubits SourceTermCompilation.sourceQubits
    SourceSimulation.smallQubits
  omega

end Paper25.FullReflectionPlacement
