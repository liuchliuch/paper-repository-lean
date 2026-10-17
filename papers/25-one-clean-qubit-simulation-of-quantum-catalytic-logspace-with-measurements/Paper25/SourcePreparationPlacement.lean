import Paper25.PreparationCompilation

/-! Place the genuine F preparation into the native coherent source filter.
The physical order is phase, rotation, h, four block ancillas, clock, and two
copies of the original source register. Every coordinate map is induced by an
explicit permutation or injection of qubit positions. -/
noncomputable section
open Matrix
namespace Paper25.SourcePreparationPlacement
open OperationalModel OperationalModel.LocalCompilation
open SourceCoordinates SourceTermCompilation StatePreparation
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1800000
set_option synthInstance.maxSize 512
variable {G : EffectiveGateSet}

abbrev WPos (S : EffectiveSourceComputation G) := Fin (restQubits S+1)
abbrev CPos (S : EffectiveSourceComputation G) := Fin S.catalystQubits
abbrev BPos := Fin 1 ⊕ Fin 3
abbrev DPos (S : EffectiveSourceComputation G) := (WPos S ⊕ CPos S) ⊕ (WPos S ⊕ CPos S)
abbrev FPos (S : EffectiveSourceComputation G) (ell : ℕ) :=
  StatePreparationLocal.FPositions ell (restQubits S) 0
abbrev UnusedPos (S : EffectiveSourceComputation G) (m : ℕ) :=
  Fin m ⊕ (Fin 1 ⊕ (BPos ⊕ (CPos S ⊕ CPos S)))
abbrev RawPos (S : EffectiveSourceComputation G) (ell m : ℕ) :=
  Fin m ⊕ (Fin 1 ⊕ (Fin 1 ⊕ (BPos ⊕ (Fin ell ⊕ DPos S))))

def outputPosition (S : EffectiveSourceComputation G) :
    Fin 1 ≃ {j : Fin S.workQubits // j=S.outputQubit} where
  toFun _ := ⟨S.outputQubit,rfl⟩
  invFun _ := 0
  left_inv _ := Subsingleton.elim _ _
  right_inv j := by apply Subtype.ext; exact j.2.symm

/-- Canonical output-first work positions, using the explicit skip-output map. -/
def workWire (S : EffectiveSourceComputation G) : WPos S ≃ Fin S.workQubits :=
  (StatePreparationLocal.splitPosition (restQubits S)).trans
    (((outputPosition S).sumCongr (otherPositions S)).trans
      (Equiv.sumCompl (fun j : Fin S.workQubits => j=S.outputQubit)))

@[simp] lemma workWire_zero (S : EffectiveSourceComputation G) :
    workWire S 0 = S.outputQubit := rfl

@[simp] lemma workWire_succ (S : EffectiveSourceComputation G) (i : Fin (restQubits S)) :
    workWire S i.succ = (otherPositions S i).1 := rfl

/-- The source's physical work/catalyst positions, before doubling. -/
def sourceWire (S : EffectiveSourceComputation G) :
    (WPos S ⊕ CPos S) ≃ Fin (sourceQubits S) :=
  ((workWire S).sumCongr (Equiv.refl _)).trans finSumFinEquiv

def dataWire (S : EffectiveSourceComputation G) : DPos S ≃ Fin (sourceQubits S+sourceQubits S) :=
  ((sourceWire S).sumCongr (sourceWire S)).trans finSumFinEquiv

def encoderQubits (S : EffectiveSourceComputation G) (ell : ℕ) : ℕ :=
  1+(3+(ell+(sourceQubits S+sourceQubits S)))

def walkQubits (S : EffectiveSourceComputation G) (ell : ℕ) : ℕ := encoderQubits S ell+1

def filterQubits (S : EffectiveSourceComputation G) (ell m : ℕ) : ℕ :=
  m+(1+walkQubits S ell)

/-- Block selectors, clock, and doubled data in the native A circuit's order. -/
def encoderWire (S : EffectiveSourceComputation G) (ell : ℕ) :
    (BPos ⊕ (Fin ell ⊕ DPos S)) ≃ Fin (encoderQubits S ell) :=
  (Equiv.sumAssoc _ _ _).trans
    (StatePreparationLocal.tensorWire (Equiv.refl (Fin 1))
      (StatePreparationLocal.tensorWire (Equiv.refl (Fin 3))
        (StatePreparationLocal.tensorWire (Equiv.refl (Fin ell)) (dataWire S))))

/-- The dilation h qubit is the first physical bit of q+1, as in probeTensor. -/
def coreWire (S : EffectiveSourceComputation G) (ell : ℕ) :
    (Fin 1 ⊕ (BPos ⊕ (Fin ell ⊕ DPos S))) ≃ Fin (walkQubits S ell) :=
  ((Equiv.refl (Fin 1)).sumCongr (encoderWire S ell)).trans
    (StatePreparationLocal.splitPosition (encoderQubits S ell)).symm

def rawWire (S : EffectiveSourceComputation G) (ell m : ℕ) :
    RawPos S ell m ≃ Fin (filterQubits S ell m) :=
  StatePreparationLocal.tensorWire (Equiv.refl (Fin m))
    (StatePreparationLocal.tensorWire (Equiv.refl (Fin 1)) (coreWire S ell))

/-- Regroup positions into the selected F positions and all untouched positions. -/
def gatherPositions (S : EffectiveSourceComputation G) (ell m : ℕ) :
    (FPos S ell ⊕ UnusedPos S m) ≃ RawPos S ell m where
  toFun p := match p with
    | .inl (.inl h) => .inr (.inr (.inl h))
    | .inl (.inr (.inl c)) => .inr (.inr (.inr (.inr (.inl c))))
    | .inl (.inr (.inr (.inl (.inl w)))) => .inr (.inr (.inr (.inr (.inr (.inl (.inl w))))))
    | .inl (.inr (.inr (.inl (.inr w)))) => .inr (.inr (.inr (.inr (.inr (.inr (.inl w))))))
    | .inl (.inr (.inr (.inr a))) => Fin.elim0 a
    | .inr (.inl p) => .inl p
    | .inr (.inr (.inl r)) => .inr (.inl r)
    | .inr (.inr (.inr (.inl b))) => .inr (.inr (.inr (.inl b)))
    | .inr (.inr (.inr (.inr (.inl c)))) => .inr (.inr (.inr (.inr (.inr (.inl (.inr c))))))
    | .inr (.inr (.inr (.inr (.inr c)))) => .inr (.inr (.inr (.inr (.inr (.inr (.inr c))))))
  invFun p := match p with
    | .inl p => .inr (.inl p)
    | .inr (.inl r) => .inr (.inr (.inl r))
    | .inr (.inr (.inl h)) => .inl (.inl h)
    | .inr (.inr (.inr (.inl b))) => .inr (.inr (.inr (.inl b)))
    | .inr (.inr (.inr (.inr (.inl c)))) => .inl (.inr (.inl c))
    | .inr (.inr (.inr (.inr (.inr (.inl (.inl w)))))) => .inl (.inr (.inr (.inl (.inl w))))
    | .inr (.inr (.inr (.inr (.inr (.inr (.inl w)))))) => .inl (.inr (.inr (.inl (.inr w))))
    | .inr (.inr (.inr (.inr (.inr (.inl (.inr c)))))) => .inr (.inr (.inr (.inr (.inl c))))
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr c)))))) => .inr (.inr (.inr (.inr (.inr c))))
  left_inv p := by
    rcases p with f | u
    · rcases f with h | (c | ((w | w) | a)) <;> first | rfl | exact Fin.elim0 a
    · rcases u with p | (r | (b | (c | c))) <;> rfl
  right_inv p := by
    rcases p with p | (r | (h | (b | (c | ((w | c) | (w | c)))))) <;> rfl

/-- The complete layout is a permutation of physical positions alone. -/
def allPositions (S : EffectiveSourceComputation G) (ell m : ℕ) :
    (FPos S ell ⊕ UnusedPos S m) ≃ Fin (filterQubits S ell m) :=
  (gatherPositions S ell m).trans (rawWire S ell m)

def readBy {a b : Type*} (e : a ≃ b) : (b → OperationalModel.Bit) ≃ (a → OperationalModel.Bit) where
  toFun x i := x (e i)
  invFun y j := y (e.symm j)
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

def splitRead (a b : Type*) : ((a ⊕ b) → OperationalModel.Bit) ≃
    ((a → OperationalModel.Bit) × (b → OperationalModel.Bit)) where
  toFun x := (fun i => x (.inl i),fun j => x (.inr j))
  invFun x := Sum.elim x.1 x.2
  left_inv x := by funext j; cases j <;> rfl
  right_inv x := rfl

/-- The F tensor coordinates are themselves induced by the proved FWire map. -/
def smallRead (S : EffectiveSourceComputation G) (ell : ℕ) :
    Small ell (restQubits S) 0 ≃ (FPos S ell → OperationalModel.Bit) :=
  (StatePreparationLocal.FLayout ell (restQubits S) 0).symm.trans
    (readBy (StatePreparationLocal.FWire ell (restQubits S) 0))

lemma smallRead_apply (S : EffectiveSourceComputation G) (ell : ℕ)
    (x : Small ell (restQubits S) 0) (j : FPos S ell) :
    smallRead S ell x j = StatePreparationLocal.FRead ell (restQubits S) 0 x j := by
  have h := StatePreparationLocal.FLayout_induced ell (restQubits S) 0
    ((StatePreparationLocal.FLayout ell (restQubits S) 0).symm x) j
  simpa only [Equiv.apply_symm_apply] using h.symm

abbrev Untouched (S : EffectiveSourceComputation G) (m : ℕ) := UnusedPos S m → OperationalModel.Bit
instance untouchedDecidableEq (S : EffectiveSourceComputation G) (m : ℕ) : DecidableEq (Untouched S m) :=
  Fintype.decidablePiFintype

/-- Full physical-to-logical coordinates, with the F register separated from
phase, rotation, block selectors, and both catalyst copies. -/
def logicalLayout (S : EffectiveSourceComputation G) (ell m : ℕ) :
    Basis (filterQubits S ell m) ≃ (Small ell (restQubits S) 0 × Untouched S m) :=
  (readBy (allPositions S ell m)).trans
    ((splitRead _ _).trans ((smallRead S ell).symm.prodCongr (Equiv.refl _)))

lemma logicalLayout_selected (S : EffectiveSourceComputation G) (ell m : ℕ)
    (x : Basis (filterQubits S ell m)) (j : FPos S ell) :
    StatePreparationLocal.FRead ell (restQubits S) 0 (logicalLayout S ell m x).1 j =
      x (allPositions S ell m (.inl j)) := by
  rw [←smallRead_apply]
  exact congrFun ((smallRead S ell).apply_symm_apply _) j

lemma logicalLayout_unused (S : EffectiveSourceComputation G) (ell m : ℕ)
    (x : Basis (filterQubits S ell m)) (j : UnusedPos S m) :
    (logicalLayout S ell m x).2 j = x (allPositions S ell m (.inr j)) := rfl

/-- The actual physical F wires, with no initialized workspace. -/
def selectedEmbedding (S : EffectiveSourceComputation G) (ell m : ℕ) :
    Fin (StatePreparationLocal.physicalSize ell (restQubits S) 0) ↪
      Fin (filterQubits S ell m) where
  toFun i := allPositions S ell m (.inl ((StatePreparationLocal.FWire ell (restQubits S) 0).symm i))
  inj' := by
    intro i j h
    exact (StatePreparationLocal.FWire ell (restQubits S) 0).symm.injective
      (Sum.inl_injective ((allPositions S ell m).injective h))

lemma selected_layout (S : EffectiveSourceComputation G) (ell m : ℕ)
    (x : Basis (filterQubits S ell m)) :
    StatePreparationLocal.FLayout ell (restQubits S) 0 (fun i => x (selectedEmbedding S ell m i)) =
      (logicalLayout S ell m x).1 := by
  apply (smallRead S ell).injective
  funext j
  simp only [smallRead_apply,StatePreparationLocal.FLayout_induced,logicalLayout_selected,
    selectedEmbedding,Function.Embedding.coeFn_mk,Equiv.symm_apply_apply]

lemma inactive_selected (S : EffectiveSourceComputation G) (ell m : ℕ)
    (x y : Basis (filterQubits S ell m)) :
    Inactive (selectedEmbedding S ell m) x y ↔
      (logicalLayout S ell m x).2 = (logicalLayout S ell m y).2 := by
  constructor
  · intro h
    funext u
    rw [logicalLayout_unused,logicalLayout_unused]
    apply h
    rintro ⟨i,hi⟩
    have he := (allPositions S ell m).injective hi
    exact Sum.noConfusion he
  · intro h j hj
    have he := (allPositions S ell m).apply_symm_apply j
    rcases hp : (allPositions S ell m).symm j with f | u
    · exfalso
      apply hj
      refine ⟨StatePreparationLocal.FWire ell (restQubits S) 0 f,?_⟩
      simpa only [selectedEmbedding,Function.Embedding.coeFn_mk,Equiv.symm_apply_apply,hp] using he
    · have hu := congrFun h u
      rw [logicalLayout_unused,logicalLayout_unused] at hu
      have hjj : allPositions S ell m (.inr u) = j := by simpa only [hp] using he
      simpa only [hjj] using hu

def placedF (conv : GateConvention G) (S : EffectiveSourceComputation G) (ell m : ℕ)
    (t : Bits ell) : EffectiveCircuit G (filterQubits S ell m) :=
  embedCircuit (placementOfEmbedding (selectedEmbedding S ell m))
    (nativeF conv ell (restQubits S) 0 t)

/-- Exact full-space matrix bridge. Every auxiliary and catalyst position is
untouched, and only h, clock and the two actual work copies see F. -/
theorem placedF_matrix (conv : GateConvention G) (S : EffectiveSourceComputation G)
    (ell m : ℕ) (t : Bits ell) :
    (placedF conv S ell m t).matrix =
      (Matrix.kronecker (F ell (restQubits S) 0 t) (1 : Matrix (Untouched S m) (Untouched S m) ℂ)).submatrix
        (logicalLayout S ell m) (logicalLayout S ell m) := by
  rw [placedF,embedCircuit_matrix,nativeF_matrix]
  ext x y
  rw [lift_apply]
  simp only [active_placementOfEmbedding_eq,Matrix.submatrix_apply,selected_layout,
    inactive_selected,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply]

theorem placedF_length (conv : GateConvention G) (S : EffectiveSourceComputation G)
    (ell m : ℕ) (t : Bits ell) :
    (placedF conv S ell m t).length ≤ preparationCost conv*(ell+2*restQubits S+6) := by
  rw [placedF,embedCircuit_length]
  exact nativeF_length conv ell (restQubits S) 0 t


abbrev RawUnused (S : EffectiveSourceComputation G) (m : ℕ) :=
  Bits m × (OperationalModel.Bit × ((OperationalModel.Bit × Bits 3) ×
    (Bits S.catalystQubits × Bits S.catalystQubits)))

/-- Read every untouched physical register in its actual order. -/
def unusedReadIndex (S : EffectiveSourceComputation G) (m : ℕ) :
    Untouched S m ≃ RawUnused S m where
  toFun u := ((fun i => u (.inl i)),
    (u (.inr (.inl 0)),
      ((u (.inr (.inr (.inl (.inl 0)))),fun i => u (.inr (.inr (.inl (.inr i))))),
       ((fun i => u (.inr (.inr (.inr (.inl i))))),
        (fun i => u (.inr (.inr (.inr (.inr i)))))))))
  invFun p := fun j => match j with
    | .inl i => p.1 i
    | .inr (.inl _) => p.2.1
    | .inr (.inr (.inl (.inl _))) => p.2.2.1.1
    | .inr (.inr (.inl (.inr i))) => p.2.2.1.2 i
    | .inr (.inr (.inr (.inl i))) => p.2.2.2.1 i
    | .inr (.inr (.inr (.inr i))) => p.2.2.2.2 i
  left_inv u := by
    funext j
    rcases j with p | (r | ((a | b) | (c | c))) <;>
      first | rfl | fin_cases r; rfl | fin_cases a; rfl
  right_inv p := rfl

/-- Pack rotation, phase, and four original block ancillas exactly as in
ActualFilterImplementation.coherentAuxBits, before its binary enumeration. -/
def packAux (m : ℕ) :
    (Bits m × (OperationalModel.Bit × (OperationalModel.Bit × Bits 3))) ≃ Bits (m+4+1) :=
  ({toFun := fun p => (p.2.1,(p.1,p.2.2))
    invFun := fun p => (p.2.1,(p.1,p.2.2))
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl} :
      (Bits m × (OperationalModel.Bit × (OperationalModel.Bit × Bits 3))) ≃
        (OperationalModel.Bit × (Bits m × (OperationalModel.Bit × Bits 3)))).trans
    (((Equiv.refl OperationalModel.Bit).prodCongr
      (((Equiv.refl (Bits m)).prodCongr (splitBits 3).symm).trans
        (registerBasis m 4).symm)).trans (splitBits (m+4)).symm)

def unusedRegroup (S : EffectiveSourceComputation G) (m : ℕ) :
    RawUnused S m ≃
      ((Bits m × (OperationalModel.Bit × (OperationalModel.Bit × Bits 3))) ×
        (Bits S.catalystQubits × Bits S.catalystQubits)) where
  toFun p := ((p.1,(p.2.1,p.2.2.1)),p.2.2.2)
  invFun p := (p.1.1,(p.1.2.1,(p.1.2.2,p.2)))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Catalyst enumeration is solely a coordinate interpretation; its physical
positions are untouched by the native F list. -/
def unusedIndex (S : EffectiveSourceComputation G) (m : ℕ) :
    Untouched S m ≃ (Bits (m+4+1) × SourceSimulation.CatalystData S.catalystQubits) :=
  (unusedReadIndex S m).trans ((unusedRegroup S m).trans
    ((packAux m).prodCongr (SourceBias.operatorIndex (Bits S.catalystQubits)).symm))

def filterRegroup (S : EffectiveSourceComputation G) (ell m : ℕ) :
    (Small ell (restQubits S) 0 ×
      (Bits (m+4+1) × SourceSimulation.CatalystData S.catalystQubits)) ≃
        SourceSimulation.FilterSpace ell (restQubits S) S.catalystQubits (m+4+1) where
  toFun p := ((p.2.1,p.1),p.2.2)
  invFun p := (p.1.2,(p.1.1,p.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Full native coherent-filter coordinates in the existing FilterSpace type. -/
def filterLayout (S : EffectiveSourceComputation G) (ell m : ℕ) :
    Basis (filterQubits S ell m) ≃
      SourceSimulation.FilterSpace ell (restQubits S) S.catalystQubits (m+4+1) :=
  (logicalLayout S ell m).trans
    (((Equiv.refl _).prodCongr (unusedIndex S m)).trans (filterRegroup S ell m))

lemma filterLayout_small (S : EffectiveSourceComputation G) (ell m : ℕ)
    (x : Basis (filterQubits S ell m)) :
    (filterLayout S ell m x).1.2 = (logicalLayout S ell m x).1 := rfl

/-- Exactly I_aux tensor F tensor I_catalyst, in the same logical type used by
the existing source/filter probability theorem. -/
theorem placedF_matrix_filterLayout (conv : GateConvention G) (S : EffectiveSourceComputation G)
    (ell m : ℕ) (t : Bits ell) :
    (placedF conv S ell m t).matrix =
      (Matrix.kronecker
        (Matrix.kronecker (1 : Matrix (Bits (m+4+1)) (Bits (m+4+1)) ℂ)
          (F ell (restQubits S) 0 t))
        (1 : Matrix (SourceSimulation.CatalystData S.catalystQubits)
          (SourceSimulation.CatalystData S.catalystQubits) ℂ)).submatrix
            (filterLayout S ell m) (filterLayout S ell m) := by
  rw [placedF_matrix]
  ext x y
  change F ell (restQubits S) 0 t (logicalLayout S ell m x).1 (logicalLayout S ell m y).1 *
    (if (logicalLayout S ell m x).2 = (logicalLayout S ell m y).2 then 1 else 0) =
      (if (unusedIndex S m (logicalLayout S ell m x).2).1 =
        (unusedIndex S m (logicalLayout S ell m y).2).1 then 1 else 0) *
      F ell (restQubits S) 0 t (logicalLayout S ell m x).1 (logicalLayout S ell m y).1 *
      (if (unusedIndex S m (logicalLayout S ell m x).2).2 =
        (unusedIndex S m (logicalLayout S ell m y).2).2 then 1 else 0)
  have he : (logicalLayout S ell m x).2 = (logicalLayout S ell m y).2 ↔
      (unusedIndex S m (logicalLayout S ell m x).2).1 =
        (unusedIndex S m (logicalLayout S ell m y).2).1 ∧
      (unusedIndex S m (logicalLayout S ell m x).2).2 =
        (unusedIndex S m (logicalLayout S ell m y).2).2 := by
    rw [← (unusedIndex S m).injective.eq_iff,Prod.mk.injEq]
  simp only [he]
  split_ifs <;> simp_all

lemma allPositions_h_val (S : EffectiveSourceComputation G) (ell m : ℕ) :
    (allPositions S ell m (.inl (.inl 0))).val = m+1 := by
  change m+(1+0) = m+1
  omega

lemma allPositions_clock_val (S : EffectiveSourceComputation G) (ell m : ℕ) (i : Fin ell) :
    (allPositions S ell m (.inl (.inr (.inl i)))).val = m+6+i.val := by
  change m+(1+((1+(3+i.val))+1)) = _
  omega

lemma allPositions_leftWork_val (S : EffectiveSourceComputation G) (ell m : ℕ) (i : WPos S) :
    (allPositions S ell m (.inl (.inr (.inr (.inl (.inl i)))))).val =
      m+6+ell+(workWire S i).val := by
  change m+(1+((1+(3+(ell+(workWire S i).val)))+1)) = _
  omega

lemma allPositions_rightWork_val (S : EffectiveSourceComputation G) (ell m : ℕ) (i : WPos S) :
    (allPositions S ell m (.inl (.inr (.inr (.inl (.inr i)))))).val =
      m+6+ell+sourceQubits S+(workWire S i).val := by
  change m+(1+((1+(3+(ell+(sourceQubits S+(workWire S i).val))))+1)) = _
  omega

lemma allPositions_phase_val (S : EffectiveSourceComputation G) (ell m : ℕ) (i : Fin m) :
    (allPositions S ell m (.inr (.inl i))).val = i.val := rfl

lemma allPositions_rotation_val (S : EffectiveSourceComputation G) (ell m : ℕ) :
    (allPositions S ell m (.inr (.inr (.inl 0)))).val = m := by
  change m+0 = m
  omega

lemma allPositions_blockOuter_val (S : EffectiveSourceComputation G) (ell m : ℕ) :
    (allPositions S ell m (.inr (.inr (.inr (.inl (.inl 0)))))).val = m+2 := by
  change m+(1+(0+1)) = m+2
  omega

lemma allPositions_blockLCU_val (S : EffectiveSourceComputation G) (ell m : ℕ) (i : Fin 3) :
    (allPositions S ell m (.inr (.inr (.inr (.inl (.inr i)))))).val = m+3+i.val := by
  change m+(1+((1+i.val)+1)) = _
  omega

lemma allPositions_leftCatalyst_val (S : EffectiveSourceComputation G) (ell m : ℕ) (i : CPos S) :
    (allPositions S ell m (.inr (.inr (.inr (.inr (.inl i)))))).val =
      m+6+ell+S.workQubits+i.val := by
  change m+(1+((1+(3+(ell+(S.workQubits+i.val))))+1)) = _
  omega

lemma allPositions_rightCatalyst_val (S : EffectiveSourceComputation G) (ell m : ℕ) (i : CPos S) :
    (allPositions S ell m (.inr (.inr (.inr (.inr (.inr i)))))).val =
      m+6+ell+sourceQubits S+S.workQubits+i.val := by
  change m+(1+((1+(3+(ell+(sourceQubits S+(S.workQubits+i.val)))))+1)) = _
  omega

end Paper25.SourcePreparationPlacement
