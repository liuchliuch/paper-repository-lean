import ELV.RayVectors
import ELV.HilbertSeparable

/-! Operational signed-Gram realization on actual oracle query spaces. -/
noncomputable section
open scoped ENNReal
namespace ELV.Costs
open ELV.Stabilize ELV.Query ELV.Model

lemma public_basis_inner (b c : Fin 2) :
    inner ℂ (publicBasis b) (publicBasis c) = if b = c then 1 else 0 :=
  orthonormal_iff_ite.mp (EuclideanSpace.basisFun (Fin 2) ℂ).orthonormal b c

lemma public_gram_difference (b c : Fin 2) :
    inner ℂ (publicBasis 0) (publicBasis 0) - inner ℂ (publicBasis b) (publicBasis c) =
      if b = c then 0 else 1 := by
  rw [public_basis_inner, public_basis_inner]
  split_ifs <;> simp_all

variable {gap : Gap} {n : ℕ} [NeZero n] {C : Type}
variable (f g : promisedFamily n gap.δ → lp (fun _ : C => ℂ) 2)

def witnessQueries (O : promisedFamily n gap.δ) : OracleQuerySpace n C :=
  rayVector (f O) (g O) (knownInput n) O.val.phi

lemma signedGram_to_witness (h : AdmissibleWitness gap.δ f g) :
    Query.Witness (fun O : promisedFamily n gap.δ => bidirectional C O.val)
      (fun _ => publicBasis 0) (fun O => publicBasis (label gap.δ O)) (witnessQueries f g) := by
  intro O O'
  rw [public_gram_difference]
  change _ = inner ℂ (rayVector _ _ _ _) (rayVector _ _ _ _) -
    inner ℂ (bidirectional C O.val (rayVector _ _ _ _))
      (bidirectional C O'.val (rayVector _ _ _ _))
  rw [ray_filter]
  exact h O O'

lemma zero_raySupported (O : Oracle n) : RaySupported O (0 : OracleQuerySpace n C) := by
  refine ⟨0,0,?_⟩
  intro i
  simp

/-- Proposition 4.1 converse in a common square summable control space:
construct one actual fixed admissible transducer and compute its pointwise cost. -/
theorem realize_signedGram_full (h : AdmissibleWitness gap.δ f g) :
    ∃ T : Realization gap n, T.Admissible ∧
      (∀ O, T.pointwiseCost O = ENNReal.ofReal (‖f O‖ ^ 2 + ‖g O‖ ^ 2)) ∧
      (Countable C → TopologicalSpace.SeparableSpace T.Private) := by
  let Q := OracleQuerySpace n C
  let v := witnessQueries f g
  have hw := signedGram_to_witness f g h
  obtain ⟨I,bV,_⟩ := exists_hilbertBasis ℂ (HilbertPair Public Q)
  let T : Realization gap n :=
    { Control := C
      Private := CanonicalPrivate I Public Q
      Nonquery := HilbertPair Public (Gram.StabilizingSpace I)
      circuit := canonicalCircuit bV hw
      catalyst := canonicalCatalyst v
      exact := canonical_exact bV hw }
  refine ⟨T, ?_, ?_, ?_⟩
  · intro O i
    fin_cases i
    · change RaySupported O.val (v O)
      exact ⟨f O, g O, fun _ => ⟨rfl,rfl⟩⟩
    · change RaySupported O.val (0 : Q)
      exact zero_raySupported O.val
  · intro O
    change ENNReal.ofReal (Query.cost (bidirectional C O.val) (canonicalCircuit bV hw)
      (WithLp.toLp 2 (publicBasis 0, canonicalCatalyst v O))) = _
    rw [canonical_cost bV hw O]
    congr 1
    exact rayVector_norm_sq (f O) (g O) (knownInput n) O.val.phi
      (knownInput_norm n) O.val.phi_norm

  · intro hC
    letI := hC
    letI : TopologicalSpace.SeparableSpace Q := Query.lp_separable
    letI : Countable I := Gram.hilbertBasis_countable bV
    letI : TopologicalSpace.SeparableSpace (Gram.StabilizingSpace I) := Gram.stabilizingSpace_separable I
    change TopologicalSpace.SeparableSpace (CanonicalPrivate I Public Q)
    infer_instance

/-- Signed-Gram realization without a separability hypothesis. -/
theorem realize_signedGram (h : AdmissibleWitness gap.δ f g) :
    ∃ T : Realization gap n, T.Admissible ∧
      ∀ O, T.pointwiseCost O = ENNReal.ofReal (‖f O‖ ^ 2 + ‖g O‖ ^ 2) := by
  obtain ⟨T,hT,hcost,_⟩ := realize_signedGram_full f g h
  exact ⟨T,hT,hcost⟩

/-- Every Hilbert witness space is allowed: choose a Hilbert basis and
represent it as square summable controls, preserving all Gram entries and costs. -/
theorem realize_signedGram_hilbert {K : Type} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K]
    (f g : promisedFamily n gap.δ → K) (h : AdmissibleWitness gap.δ f g) :
    ∃ T : Realization gap n, T.Admissible ∧
      ∀ O, T.pointwiseCost O = ENNReal.ofReal (‖f O‖ ^ 2 + ‖g O‖ ^ 2) := by
  obtain ⟨I,bK,_⟩ := exists_hilbertBasis ℂ K
  have hc : AdmissibleWitness gap.δ (fun O => bK.repr (f O)) (fun O => bK.repr (g O)) := by
    intro O O'
    simpa only [bK.repr.inner_map_map] using h O O'
  obtain ⟨T,hT,hcost⟩ := realize_signedGram (fun O => bK.repr (f O)) (fun O => bK.repr (g O)) hc
  exact ⟨T,hT,fun O => by simpa only [bK.repr.norm_map] using hcost O⟩

/-- Separable Hilbert witnesses have an actual realization with separable private space. -/
theorem realize_signedGram_separable {K : Type} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] [TopologicalSpace.SeparableSpace K]
    (f g : promisedFamily n gap.δ → K) (h : AdmissibleWitness gap.δ f g) :
    ∃ T : Realization gap n, T.Admissible ∧
      (∀ O, T.pointwiseCost O = ENNReal.ofReal (‖f O‖ ^ 2 + ‖g O‖ ^ 2)) ∧
      TopologicalSpace.SeparableSpace T.Private := by
  obtain ⟨I,bK,_⟩ := exists_hilbertBasis ℂ K
  letI : Countable I := Gram.hilbertBasis_countable bK
  have hc : AdmissibleWitness gap.δ (fun O => bK.repr (f O)) (fun O => bK.repr (g O)) := by
    intro O O'
    simpa only [bK.repr.inner_map_map] using h O O'
  obtain ⟨T,hT,hcost,hsep⟩ := realize_signedGram_full (fun O => bK.repr (f O))
    (fun O => bK.repr (g O)) hc
  exact ⟨T,hT,(fun O => by simpa only [bK.repr.norm_map] using hcost O),hsep inferInstance⟩

/-- Extract signed-Gram witnesses from every actual admissible finite circuit.
Query-time labels form an orthogonal finite direct sum of the actual controls. -/
theorem extract_signedGram_full (T : Realization gap n) (hT : T.Admissible) :
    ∃ f g : promisedFamily n gap.δ →
        PiLp 2 (fun _ : Fin T.circuit.length => lp (fun _ : T.Control => ℂ) 2),
      AdmissibleWitness gap.δ f g ∧
      (∀ O, T.pointwiseCost O = ENNReal.ofReal (‖f O‖ ^ 2 + ‖g O‖ ^ 2)) ∧
      ∀ O i, Query.trace (bidirectional T.Control O.val) T.circuit
        (WithLp.toLp 2 (publicBasis 0,T.catalyst O)) i =
          rayVector (f O i) (g O i) (knownInput n) O.val.phi := by
  classical
  have hsupport := fun O i => (raySupported_iff O.val _).1 (hT O i)
  choose F G hFG using hsupport
  let f := fun O => WithLp.toLp 2 (F O)
  let g := fun O => WithLp.toLp 2 (G O)
  refine ⟨f,g,?_,?_,?_⟩
  · intro O O'
    have ht := Query.adversary_identity T.circuit
      (fun O : promisedFamily n gap.δ => bidirectional T.Control O.val)
      (fun _ => publicBasis 0) (fun O => publicBasis (label gap.δ O)) T.catalyst T.exact O O'
    rw [public_gram_difference] at ht
    simp_rw [hFG O, hFG O', ray_filter] at ht
    rw [ht]
    change (∑ j, (1 - inner ℂ O.val.phi O'.val.phi) *
        (inner ℂ (F O j) (F O' j) - inner ℂ (G O j) (G O' j))) =
      (1 - inner ℂ O.val.phi O'.val.phi) *
        ((∑ j, inner ℂ (F O j) (F O' j)) - ∑ j, inner ℂ (G O j) (G O' j))
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  · intro O
    change ENNReal.ofReal (Query.cost _ _ _) = _
    congr 1
    unfold Query.cost
    simp_rw [hFG O]
    simp_rw [rayVector_norm_sq _ _ _ _ (knownInput_norm n) O.val.phi_norm]
    have hf : ‖f O‖ ^ 2 = ∑ j, ‖F O j‖ ^ 2 := PiLp.norm_sq_eq_of_L2 _ _
    have hg : ‖g O‖ ^ 2 = ∑ j, ‖G O j‖ ^ 2 := PiLp.norm_sq_eq_of_L2 _ _
    rw [hf,hg,Finset.sum_add_distrib]

  · exact hFG

/-- Extract just the feasible family and exact pointwise costs. -/
theorem extract_signedGram (T : Realization gap n) (hT : T.Admissible) :
    ∃ f g : promisedFamily n gap.δ →
        PiLp 2 (fun _ : Fin T.circuit.length => lp (fun _ : T.Control => ℂ) 2),
      AdmissibleWitness gap.δ f g ∧
      ∀ O, T.pointwiseCost O = ENNReal.ofReal (‖f O‖ ^ 2 + ‖g O‖ ^ 2) := by
  obtain ⟨f,g,hfg,hcost,_⟩ := extract_signedGram_full T hT
  exact ⟨f,g,hfg,hcost⟩

/-- Feasible signed-Gram families on arbitrary complete Hilbert spaces. -/
structure SignedFamily (gap : Gap) (n : ℕ) [NeZero n] where
  K : Type
  [normK : NormedAddCommGroup K]
  [innerK : InnerProductSpace ℂ K]
  [completeK : CompleteSpace K]
  f : promisedFamily n gap.δ → K
  g : promisedFamily n gap.δ → K
  feasible : AdmissibleWitness gap.δ f g

attribute [instance] SignedFamily.normK SignedFamily.innerK SignedFamily.completeK

def signedValue (gap : Gap) (n : ℕ) [NeZero n] : ℝ≥0∞ :=
  sInf {c | ∃ W : SignedFamily gap n, uniformWitnessCost gap.δ W.f W.g = c}

/-- Proposition 4.1: equality of operational minimax and Hilbert-space
signed-Gram optimization, proved by constructing/extracting actual circuits. -/
theorem admissible_adversary (gap : Gap) (n : ℕ) [NeZero n] :
    C_adm gap n = signedValue gap n := by
  unfold C_adm signedValue
  congr 1
  ext c
  constructor
  · rintro ⟨T,hT,hc⟩
    obtain ⟨f,g,hfg,hcost⟩ := extract_signedGram T hT
    refine ⟨{ K := _, f := f, g := g, feasible := hfg }, ?_⟩
    change uniformWitnessCost gap.δ f g = c
    rw [← hc]
    unfold uniformWitnessCost Realization.uniformCost
    apply iSup_congr
    intro O
    exact (hcost O).symm
  · rintro ⟨W,hc⟩
    obtain ⟨T,hT,hcost⟩ := realize_signedGram_hilbert W.f W.g W.feasible
    refine ⟨T,hT,?_⟩
    rw [← hc]
    unfold uniformWitnessCost Realization.uniformCost
    apply iSup_congr
    intro O
    exact hcost O

/-- Different forward and inverse Hilbert control spaces are embedded into
their orthogonal direct sum before constructing the same fixed circuit. -/
theorem realize_signedGram_twoSpaces {Kf Kg : Type}
    [NormedAddCommGroup Kf] [InnerProductSpace ℂ Kf] [CompleteSpace Kf]
    [NormedAddCommGroup Kg] [InnerProductSpace ℂ Kg] [CompleteSpace Kg]
    (f : promisedFamily n gap.δ → Kf) (g : promisedFamily n gap.δ → Kg)
    (h : AdmissibleWitness gap.δ f g) :
    ∃ T : Realization gap n, T.Admissible ∧
      ∀ O, T.pointwiseCost O = ENNReal.ofReal (‖f O‖ ^ 2 + ‖g O‖ ^ 2) := by
  let f' := fun O => WithLp.toLp 2 (f O,(0 : Kg))
  let g' := fun O => WithLp.toLp 2 ((0 : Kf),g O)
  have hc : AdmissibleWitness gap.δ f' g' := by
    intro O O'
    simpa [f',g',WithLp.prod_inner_apply] using h O O'
  obtain ⟨T,hT,hcost⟩ := realize_signedGram_hilbert f' g' hc
  refine ⟨T,hT,?_⟩
  intro O
  rw [hcost O]
  simp [f',g',WithLp.prod_norm_sq_eq_of_L2]

/-- The two separate Hilbert spaces exactly as stated in Proposition 4.1. -/
structure TwoSpaceFamily (gap : Gap) (n : ℕ) [NeZero n] where
  Kf : Type
  Kg : Type
  [normF : NormedAddCommGroup Kf]
  [innerF : InnerProductSpace ℂ Kf]
  [completeF : CompleteSpace Kf]
  [normG : NormedAddCommGroup Kg]
  [innerG : InnerProductSpace ℂ Kg]
  [completeG : CompleteSpace Kg]
  f : promisedFamily n gap.δ → Kf
  g : promisedFamily n gap.δ → Kg
  feasible : AdmissibleWitness gap.δ f g

attribute [instance] TwoSpaceFamily.normF TwoSpaceFamily.innerF TwoSpaceFamily.completeF
  TwoSpaceFamily.normG TwoSpaceFamily.innerG TwoSpaceFamily.completeG

def twoSpaceValue (gap : Gap) (n : ℕ) [NeZero n] : ENNReal :=
  sInf {c | ∃ W : TwoSpaceFamily gap n, uniformWitnessCost gap.δ W.f W.g = c}

/-- Full Proposition 4.1 with independently chosen forward and inverse controls. -/
theorem admissible_adversary_twoSpaces (gap : Gap) (n : ℕ) [NeZero n] :
    C_adm gap n = twoSpaceValue gap n := by
  unfold C_adm twoSpaceValue
  congr 1
  ext c
  constructor
  · rintro ⟨T,hT,hc⟩
    obtain ⟨f,g,hfg,hcost⟩ := extract_signedGram T hT
    refine ⟨{ Kf := _, Kg := _, f := f, g := g, feasible := hfg }, ?_⟩
    change uniformWitnessCost gap.δ f g = c
    rw [← hc]
    unfold uniformWitnessCost Realization.uniformCost
    exact iSup_congr fun O => (hcost O).symm
  · rintro ⟨W,hc⟩
    obtain ⟨T,hT,hcost⟩ := realize_signedGram_twoSpaces W.f W.g W.feasible
    refine ⟨T,hT,?_⟩
    rw [← hc]
    unfold uniformWitnessCost Realization.uniformCost
    exact iSup_congr hcost

end ELV.Costs
