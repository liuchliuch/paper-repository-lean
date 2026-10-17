import Paper25.StatePreparation
import Paper25.CircuitModel

/-!
# Physical local-gate implementation of the Bell and F preparations

All placements below select actual bit positions. Complement order is immaterial:
its only semantic effect is equality of untouched bit strings. Tensor embeddings
use `Fin.castAdd` and `Fin.natAdd`, never a permutation of complete basis labels.
-/
noncomputable section
open Matrix
open Paper25.OperationalModel
namespace Paper25.StatePreparationLocal
open StatePreparation

local notation "QBit" => Fin 2
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 800000

/-- The fixed alphabet H, X, Z, CNOT. -/
def elementaryArity : Fin 4 → ℕ :=
  Fin.cases 1 (Fin.cases 1 (Fin.cases 1 (fun _ => 2)))

def twoBits : Basis 2 ≃ (QBit × QBit) where
  toFun f := (f 0,f 1)
  invFun p := ![p.1,p.2]
  left_inv f := by funext i; fin_cases i <;> rfl
  right_inv p := by rcases p with ⟨a,b⟩; rfl

def elementaryMatrix : (a : Fin 4) → Operator (elementaryArity a) :=
  Fin.cases (H2.submatrix oneBit oneBit)
    (Fin.cases (X2.submatrix oneBit oneBit)
      (Fin.cases (Z2.submatrix oneBit oneBit) (fun _ => CNOT.submatrix twoBits twoBits)))

lemma elementary_unitary (a : Fin 4) : OneCleanQubit.Unitary (elementaryMatrix a) := by
  fin_cases a
  · exact unitary_reindex _ _ H2_unitary
  · exact unitary_reindex _ _ X2_unitary
  · exact unitary_reindex _ _ Z2_unitary
  · exact unitary_reindex _ _ CNOT_unitary

def elementary : GateSet where
  symbols := 4
  arity := elementaryArity
  locality := 2
  arity_le a := by fin_cases a <;> decide
  matrix := elementaryMatrix
  unitary := elementary_unitary

/-- The selected wires of an already legal placement. -/
def active {q k : ℕ} (p : Placement q k) : Fin k ↪ Fin q where
  toFun i := p.wires (Sum.inl i)
  inj' := by intro i j h; exact Sum.inl_injective (p.wires.injective h)

/-- Equality on all positions outside the selected wires. -/
def Inactive {q k : ℕ} (f : Fin k ↪ Fin q) (x y : Basis q) : Prop :=
  ∀ j, j ∉ Set.range f → x j = y j

lemma rest_eq_iff {q k : ℕ} (p : Placement q k) (x y : Basis q) :
    (p.split x).2 = (p.split y).2 ↔ Inactive (active p) x y := by
  constructor
  · intro h j hj
    have he := p.wires.apply_symm_apply j
    rcases hp : p.wires.symm j with i | i
    · exfalso
      apply hj
      exact ⟨i, by simpa only [active,hp] using he⟩
    · have hi := congrFun h i
      change x (p.wires (Sum.inr i)) = y (p.wires (Sum.inr i)) at hi
      have he' : p.wires (Sum.inr i) = j := by simpa only [hp] using he
      simpa only [he'] using hi
  · intro h
    funext i
    apply h (p.wires (Sum.inr i))
    rintro ⟨j,hj⟩
    have := p.wires.injective hj
    exact Sum.noConfusion this

lemma localGate_apply {G : GateSet} {q : ℕ} (g : LocalGate G q) (x y : Basis q) :
    g.matrix x y = G.matrix g.symbol (fun i => x (active g.placement i))
      (fun i => y (active g.placement i)) *
        (if Inactive (active g.placement) x y then 1 else 0) := by
  rw [LocalGate.matrix,Placement.lift_apply]
  simp only [rest_eq_iff]
  rfl

/-- Any injection of k physical positions can be completed by the untouched
positions; the completion is a permutation of positions alone. -/
def complementEquiv {q k : ℕ} (f : Fin k ↪ Fin q) :
    Fin (q-k) ≃ {j : Fin q // j ∉ Set.range f} := by
  classical
  have hc : Fintype.card {j : Fin q // j ∉ Set.range f} = q-k := by
    rw [Fintype.card_subtype_compl]
    simp only [Fintype.card_fin,Fintype.card_range]
  exact (finCongr hc.symm).trans (Fintype.equivFin _).symm

def placementOfEmbedding {q k : ℕ} (f : Fin k ↪ Fin q) : Placement q k := by
  classical
  exact {
    enough := by simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f f.injective
    wires := (Equiv.sumCongr f.toEquivRange (complementEquiv f)).trans
      (Equiv.sumCompl (fun j : Fin q => j ∈ Set.range f)) }

@[simp] lemma active_placementOfEmbedding {q k : ℕ} (f : Fin k ↪ Fin q) (i : Fin k) :
    active (placementOfEmbedding f) i = f i := by
  classical
  rfl

@[simp] lemma active_placementOfEmbedding_eq {q k : ℕ} (f : Fin k ↪ Fin q) :
    active (placementOfEmbedding f) = f := by
  apply Function.Embedding.ext
  intro i
  exact active_placementOfEmbedding f i

/-- Split a physical register at a position boundary. -/
def tensorBits (q r : ℕ) : Basis (q+r) ≃ (Basis q × Basis r) where
  toFun x := (fun i => x (Fin.castAdd r i),fun j => x (Fin.natAdd q j))
  invFun p := fun i => Sum.elim p.1 p.2 (finSumFinEquiv.symm i)
  left_inv x := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  right_inv p := by apply Prod.ext <;> funext i <;> simp

def leftEmbedding {q k : ℕ} (f : Fin k ↪ Fin q) (r : ℕ) : Fin k ↪ Fin (q+r) where
  toFun i := Fin.castAdd r (f i)
  inj' := by intro i j h; apply f.injective; simpa using h

def rightEmbedding {r k : ℕ} (f : Fin k ↪ Fin r) (q : ℕ) : Fin k ↪ Fin (q+r) where
  toFun i := Fin.natAdd q (f i)
  inj' := by intro i j h; apply f.injective; simpa using h

lemma inactive_left {q k r : ℕ} (f : Fin k ↪ Fin q) (x y : Basis (q+r)) :
    Inactive (leftEmbedding f r) x y ↔
      Inactive f (tensorBits q r x).1 (tensorBits q r y).1 ∧
        (tensorBits q r x).2 = (tensorBits q r y).2 := by
  constructor
  · intro h
    constructor
    · intro j hj
      apply h (Fin.castAdd r j)
      rintro ⟨i,hi⟩
      change Fin.castAdd r (f i) = Fin.castAdd r j at hi
      exact hj ⟨i,by simpa using hi⟩
    · funext j
      apply h (Fin.natAdd q j)
      rintro ⟨i,hi⟩
      have hv := congrArg Fin.val hi
      have hb := (f i).isLt
      simp [leftEmbedding] at hv
      omega
  · rintro ⟨hL,hR⟩ j
    refine Fin.addCases (fun i hi => ?_) (fun i hi => ?_) j
    · apply hL i
      rintro ⟨a,ha⟩
      exact hi ⟨a,congrArg (Fin.castAdd r) ha⟩
    · exact congrFun hR i

lemma inactive_right {q r k : ℕ} (f : Fin k ↪ Fin r) (x y : Basis (q+r)) :
    Inactive (rightEmbedding f q) x y ↔
      (tensorBits q r x).1 = (tensorBits q r y).1 ∧
        Inactive f (tensorBits q r x).2 (tensorBits q r y).2 := by
  constructor
  · intro h
    constructor
    · funext j
      apply h (Fin.castAdd r j)
      rintro ⟨i,hi⟩
      have hv := congrArg Fin.val hi
      have hb := j.isLt
      simp [rightEmbedding] at hv
      omega
    · intro j hj
      apply h (Fin.natAdd q j)
      rintro ⟨i,hi⟩
      change Fin.natAdd q (f i) = Fin.natAdd q j at hi
      exact hj ⟨i,by simpa using hi⟩
  · rintro ⟨hL,hR⟩ j
    refine Fin.addCases (fun i hi => ?_) (fun i hi => ?_) j
    · exact congrFun hL i
    · apply hR i
      rintro ⟨a,ha⟩
      exact hi ⟨a,congrArg (Fin.natAdd q) ha⟩

def liftLeft {G : GateSet} {q : ℕ} (g : LocalGate G q) (r : ℕ) : LocalGate G (q+r) where
  symbol := g.symbol
  placement := placementOfEmbedding (leftEmbedding (active g.placement) r)

def liftRight {G : GateSet} {r : ℕ} (g : LocalGate G r) (q : ℕ) : LocalGate G (q+r) where
  symbol := g.symbol
  placement := placementOfEmbedding (rightEmbedding (active g.placement) q)

lemma liftLeft_matrix {G : GateSet} {q : ℕ} (g : LocalGate G q) (r : ℕ) :
    (liftLeft g r).matrix = (Matrix.kronecker g.matrix (1 : Operator r)).submatrix
      (tensorBits q r) (tensorBits q r) := by
  ext x y
  rw [localGate_apply]
  simp only [liftLeft,active_placementOfEmbedding_eq,Matrix.submatrix_apply,
    Matrix.kronecker,Matrix.kroneckerMap_apply,localGate_apply,Matrix.one_apply,
    inactive_left]
  dsimp only [leftEmbedding,tensorBits]
  by_cases hL : Inactive (active g.placement) (fun i => x (Fin.castAdd r i))
      (fun i => y (Fin.castAdd r i)) <;>
    by_cases hR : (fun i => x (Fin.natAdd q i)) = (fun i => y (Fin.natAdd q i)) <;>
      simp [hL,hR]

lemma liftRight_matrix {G : GateSet} {r : ℕ} (g : LocalGate G r) (q : ℕ) :
    (liftRight g q).matrix = (Matrix.kronecker (1 : Operator q) g.matrix).submatrix
      (tensorBits q r) (tensorBits q r) := by
  ext x y
  rw [localGate_apply]
  simp only [liftRight,active_placementOfEmbedding_eq,Matrix.submatrix_apply,
    Matrix.kronecker,Matrix.kroneckerMap_apply,localGate_apply,Matrix.one_apply,
    inactive_right]
  dsimp only [rightEmbedding,tensorBits]
  by_cases hL : (fun i => x (Fin.castAdd r i)) = (fun i => y (Fin.castAdd r i)) <;>
    by_cases hR : Inactive (active g.placement) (fun i => x (Fin.natAdd q i))
      (fun i => y (Fin.natAdd q i)) <;> simp [hL,hR]

/-- Disjoint local circuits, represented in the actual physical qubit model. -/
def tensorCircuit {G : GateSet} {q r : ℕ} (C : Circuit G q) (D : Circuit G r) :
    Circuit G (q+r) := C.map (fun g => liftLeft g r) ++ D.map (fun g => liftRight g q)

lemma leftCircuit_matrix {G : GateSet} {q : ℕ} (C : Circuit G q) (r : ℕ) :
    Circuit.matrix (C.map (fun g => liftLeft g r)) =
      (Matrix.kronecker C.matrix (1 : Operator r)).submatrix (tensorBits q r) (tensorBits q r) := by
  induction C with
  | nil => simp [Circuit.matrix,Matrix.kronecker,Matrix.one_kronecker_one,Matrix.submatrix_one_equiv]
  | cons g gs ih =>
    simp only [List.map_cons,Circuit.matrix]
    rw [ih,liftLeft_matrix,Matrix.submatrix_mul_equiv]
    simp only [Matrix.kronecker,←Matrix.mul_kronecker_mul,one_mul]

lemma rightCircuit_matrix {G : GateSet} {r : ℕ} (D : Circuit G r) (q : ℕ) :
    Circuit.matrix (D.map (fun g => liftRight g q)) =
      (Matrix.kronecker (1 : Operator q) D.matrix).submatrix (tensorBits q r) (tensorBits q r) := by
  induction D with
  | nil => simp [Circuit.matrix,Matrix.kronecker,Matrix.one_kronecker_one,Matrix.submatrix_one_equiv]
  | cons g gs ih =>
    simp only [List.map_cons,Circuit.matrix]
    rw [ih,liftRight_matrix,Matrix.submatrix_mul_equiv]
    simp only [Matrix.kronecker,←Matrix.mul_kronecker_mul,one_mul]

lemma tensorCircuit_matrix {G : GateSet} {q r : ℕ} (C : Circuit G q) (D : Circuit G r) :
    (tensorCircuit C D).matrix = (Matrix.kronecker C.matrix D.matrix).submatrix
      (tensorBits q r) (tensorBits q r) := by
  rw [tensorCircuit,Circuit.matrix_append,leftCircuit_matrix,rightCircuit_matrix,
    Matrix.submatrix_mul_equiv]
  simp only [Matrix.kronecker,←Matrix.mul_kronecker_mul,one_mul,mul_one]

@[simp] lemma tensorCircuit_length {G : GateSet} {q r : ℕ}
    (C : Circuit G q) (D : Circuit G r) :
    (tensorCircuit C D).length = C.length + D.length := by simp [tensorCircuit]

def identityEmbedding (k : ℕ) : Fin k ↪ Fin k := ⟨id,Function.injective_id⟩

def wholeGate (a : Fin 4) : LocalGate elementary (elementaryArity a) where
  symbol := a
  placement := placementOfEmbedding (identityEmbedding _)

lemma wholeGate_matrix (a : Fin 4) : (wholeGate a).matrix = elementaryMatrix a := by
  ext x y
  rw [localGate_apply]
  simp only [wholeGate,active_placementOfEmbedding_eq]
  have hi : Inactive (identityEmbedding (elementaryArity a)) x y := by
    intro j hj
    exact False.elim (hj ⟨j,rfl⟩)
  change elementaryMatrix a x y *
    (if Inactive (identityEmbedding (elementaryArity a)) x y then 1 else 0) = _
  rw [if_pos hi,mul_one]

def hCircuit : Circuit elementary 1 := [wholeGate 0]
def xCircuit : Circuit elementary 1 := [wholeGate 1]
def zCircuit : Circuit elementary 1 := [wholeGate 2]
def cnotCircuit : Circuit elementary 2 := [wholeGate 3]

lemma hCircuit_matrix : hCircuit.matrix = H2.submatrix oneBit oneBit := by
  simp only [hCircuit,Circuit.matrix,one_mul,wholeGate_matrix]
  rfl
lemma xCircuit_matrix : xCircuit.matrix = X2.submatrix oneBit oneBit := by
  simp only [xCircuit,Circuit.matrix,one_mul,wholeGate_matrix]
  rfl
lemma zCircuit_matrix : zCircuit.matrix = Z2.submatrix oneBit oneBit := by
  simp only [zCircuit,Circuit.matrix,one_mul,wholeGate_matrix]
  rfl
lemma cnotCircuit_matrix : cnotCircuit.matrix = CNOT.submatrix twoBits twoBits := by
  simp only [cnotCircuit,Circuit.matrix,one_mul,wholeGate_matrix]
  rfl

/-- Tensor layouts are induced by the two inclusion maps of physical positions. -/
def tensorLayout {q r : ℕ} {a b : Type*} (e : Basis q ≃ a) (f : Basis r ≃ b) :
    Basis (q+r) ≃ (a × b) := (tensorBits q r).trans (e.prodCongr f)

lemma tensorCircuit_matrix_of {q r : ℕ} {a b : Type*}
    [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (C : Circuit elementary q) (D : Circuit elementary r)
    (U : Matrix a a ℂ) (V : Matrix b b ℂ) (e : Basis q ≃ a) (f : Basis r ≃ b)
    (hC : C.matrix = U.submatrix e e) (hD : D.matrix = V.submatrix f f) :
    (tensorCircuit C D).matrix = (Matrix.kronecker U V).submatrix
      (tensorLayout e f) (tensorLayout e f) := by
  rw [tensorCircuit_matrix,hC,hD]
  ext x y
  rfl

@[simp] lemma tensorBits_zero (q r : ℕ) : tensorBits q r (zeroBits (q+r)) =
    (zeroBits q,zeroBits r) := rfl

lemma tensorLayout_zero {q r : ℕ} {a b : Type*} (e : Basis q ≃ a) (f : Basis r ≃ b) :
    tensorLayout e f (zeroBits (q+r)) = (e (zeroBits q),f (zeroBits r)) := rfl

lemma tensor_oneBit : tensorLayout oneBit oneBit = twoBits := by
  apply Equiv.ext
  intro x
  apply Prod.ext
  · rfl
  · apply congrArg x
    decide

def bellLocalPair : Circuit elementary 2 :=
  tensorCircuit hCircuit ([] : Circuit elementary 1) ++ cnotCircuit

lemma bellLocalPair_matrix : bellLocalPair.matrix = bellPair.submatrix twoBits twoBits := by
  have hi : Circuit.matrix ([] : Circuit elementary 1) =
      (1 : Matrix QBit QBit ℂ).submatrix oneBit oneBit := by simp [Circuit.matrix]
  have hh := tensorCircuit_matrix_of hCircuit ([] : Circuit elementary 1) H2 1 oneBit oneBit
    hCircuit_matrix hi
  rw [tensor_oneBit] at hh
  rw [bellLocalPair,Circuit.matrix_append,cnotCircuit_matrix,hh,Matrix.submatrix_mul_equiv]
  rfl

@[simp] lemma bellLocalPair_length : bellLocalPair.length = 2 := by
  rw [bellLocalPair,List.length_append,tensorCircuit_length]
  rfl

/-- Physical order interleaves the two halves of each Bell pair. -/
def bellSize : ℕ → ℕ | 0 => 0 | s+1 => 2+bellSize s

lemma bellSize_eq (s : ℕ) : bellSize s = 2*s := by
  induction s with | zero => rfl | succ s ih => simp [bellSize,ih]; omega

def bellLayout : (s : ℕ) → Basis (bellSize s) ≃ (Bits s × Bits s)
  | 0 => {
      toFun := fun _ => (zeroBits 0,zeroBits 0)
      invFun := fun _ => zeroBits 0
      left_inv := by intro x; funext i; exact Fin.elim0 i
      right_inv := by rintro ⟨x,y⟩; apply Prod.ext <;> funext i <;> exact Fin.elim0 i }
  | s+1 => (tensorLayout twoBits (bellLayout s)).trans (pairShuffle s).symm

def bellLocal : (s : ℕ) → Circuit elementary (bellSize s)
  | 0 => []
  | s+1 => tensorCircuit bellLocalPair (bellLocal s)

lemma bellLocal_matrix (s : ℕ) : (bellLocal s).matrix =
    (bellPrep s).submatrix (bellLayout s) (bellLayout s) := by
  induction s with
  | zero => simp [bellLocal,Circuit.matrix,bellPrep,Matrix.submatrix_one_equiv]
  | succ s ih =>
    have h := tensorCircuit_matrix_of bellLocalPair (bellLocal s) bellPair (bellPrep s)
      twoBits (bellLayout s) bellLocalPair_matrix ih
    rw [bellLocal,h]
    ext x y
    simp [bellPrep,bellLayout,Matrix.submatrix_apply] <;> rfl

lemma bellLocal_length (s : ℕ) : (bellLocal s).length = 2*s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    change (tensorCircuit bellLocalPair (bellLocal s)).length = _
    rw [tensorCircuit_length,bellLocalPair_length,ih]
    omega

@[simp] lemma bellLayout_zero (s : ℕ) : bellLayout s (zeroBits (bellSize s)) =
    (zeroBits s,zeroBits s) := by
  induction s with
  | zero => rfl
  | succ s ih =>
    apply (pairShuffle s).injective
    change tensorLayout twoBits (bellLayout s) (zeroBits (2+bellSize s)) =
      pairShuffle s (zeroBits (s+1),zeroBits (s+1))
    rw [tensorLayout_zero,ih]
    rfl

lemma pullback_diagonal {a b : Type*} [DecidableEq a] [DecidableEq b]
    (e : a ≃ b) (d : b → ℂ) : (Matrix.diagonal d).submatrix e e =
      Matrix.diagonal (fun x => d (e x)) := by
  ext x y
  by_cases h : x=y <;> simp [Matrix.diagonal_apply,Matrix.submatrix_apply,h,e.injective.eq_iff]

lemma lift_mul {q k : ℕ} (p : Placement q k) (U V : Operator k) :
    p.lift U * p.lift V = p.lift (U*V) := by
  unfold Placement.lift
  rw [Matrix.submatrix_mul_equiv]
  simp only [Matrix.kronecker,←Matrix.mul_kronecker_mul,one_mul]

lemma lift_diagonal {q k : ℕ} (p : Placement q k) (d : Basis k → ℂ) :
    p.lift (Matrix.diagonal d) = Matrix.diagonal (fun x => d (p.split x).1) := by
  unfold Placement.lift
  rw [show (1 : Operator (q-k)) = Matrix.diagonal (fun _ => (1 : ℂ)) from
    Matrix.diagonal_one.symm]
  simp only [Matrix.kronecker,Matrix.diagonal_kronecker_diagonal,mul_one]
  exact pullback_diagonal p.split _

def firstWire (s : ℕ) : Fin 1 ↪ Fin (bellSize (s+1)) where
  toFun _ := ⟨0,by simp [bellSize]⟩
  inj' _ _ _ := Subsingleton.elim _ _

def firstX (s : ℕ) : LocalGate elementary (bellSize (s+1)) where
  symbol := (1 : Fin 4)
  placement := placementOfEmbedding (firstWire s)

def firstZ (s : ℕ) : LocalGate elementary (bellSize (s+1)) where
  symbol := (2 : Fin 4)
  placement := placementOfEmbedding (firstWire s)

def signLocal (s : ℕ) : Circuit elementary (bellSize (s+1)) := [firstX s,firstZ s,firstX s]

lemma signLocal_matrix (s : ℕ) : (signLocal s).matrix =
    Matrix.diagonal (fun x => SourceBias.sign (x ⟨0,by simp [bellSize]⟩)) := by
  let p := placementOfEmbedding (firstWire s)
  change ((1 * p.lift (X2.submatrix oneBit oneBit)) *
    p.lift (Z2.submatrix oneBit oneBit)) * p.lift (X2.submatrix oneBit oneBit) = _
  rw [one_mul,lift_mul,lift_mul,Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv,
    XZX_signed,pullback_diagonal,lift_diagonal]
  rfl

def signedLayout (s : ℕ) : Basis (bellSize (s+1)) ≃ (WorkSpace s × WorkSpace s) :=
  (bellLayout (s+1)).trans (workPairBasis s).symm

@[simp] lemma signedLayout_first (s : ℕ) (x : Basis (bellSize (s+1))) :
    (signedLayout s x).1.1 = x ⟨0,by simp [bellSize]⟩ := rfl

def signedLocal (s : ℕ) : Circuit elementary (bellSize (s+1)) :=
  bellLocal (s+1) ++ signLocal s

lemma signedLocal_matrix (s : ℕ) : (signedLocal s).matrix =
    (signedBellPrep s).submatrix (signedLayout s) (signedLayout s) := by
  rw [signedLocal,Circuit.matrix_append,signLocal_matrix,bellLocal_matrix,
    signedBellPrep,←Matrix.submatrix_mul_equiv (signGate s)
      ((bellPrep (s+1)).submatrix (workPairBasis s) (workPairBasis s))
      (signedLayout s) (signedLayout s) (signedLayout s),signGate_diagonal,pullback_diagonal]
  congr 1

@[simp] lemma signedLayout_zero (s : ℕ) :
    signedLayout s (zeroBits (bellSize (s+1))) = (zeroWork s,zeroWork s) := by
  simp [signedLayout,bellLayout_zero,workPairBasis,zeroWork]

lemma signedLocal_length (s : ℕ) : (signedLocal s).length = 2*s+5 := by
  simp [signedLocal,bellLocal_length,signLocal]
  omega

def clockSize : ℕ → ℕ | 0 => 0 | ell+1 => 1+clockSize ell

lemma clockSize_eq (ell : ℕ) : clockSize ell = ell := by
  induction ell with | zero => rfl | succ ell ih => simp [clockSize,ih]; omega

def clockLayout : (ell : ℕ) → Basis (clockSize ell) ≃ Bits ell
  | 0 => Equiv.refl _
  | ell+1 => (tensorLayout oneBit (clockLayout ell)).trans (splitBits ell).symm

def clockLocal : (ell : ℕ) → Bits ell → Circuit elementary (clockSize ell)
  | 0,_ => []
  | ell+1,t => tensorCircuit (if t 0 = 0 then ([] : Circuit elementary 1) else xCircuit)
      (clockLocal ell (fun i => t i.succ))

lemma clockLocal_matrix (ell : ℕ) (t : Bits ell) : (clockLocal ell t).matrix =
    (basisPrep ell t).submatrix (clockLayout ell) (clockLayout ell) := by
  induction ell with
  | zero => simp [clockLocal,Circuit.matrix,basisPrep,Matrix.submatrix_one_equiv]
  | succ ell ih =>
    have hh : Circuit.matrix (if t 0 = 0 then ([] : Circuit elementary 1) else xCircuit) =
        (if t 0 = 0 then (1 : Matrix QBit QBit ℂ) else X2).submatrix oneBit oneBit := by
      by_cases h : t 0 = 0 <;> simp [h,xCircuit_matrix,Circuit.matrix]
    have h := tensorCircuit_matrix_of _ _ _ _ oneBit (clockLayout ell) hh
      (ih (fun i => t i.succ))
    rw [clockLocal,h]
    ext x y
    simp [basisPrep,clockLayout,Matrix.submatrix_apply] <;> rfl

@[simp] lemma clockLayout_zero (ell : ℕ) : clockLayout ell (zeroBits (clockSize ell)) =
    zeroBits ell := by
  induction ell with
  | zero => rfl
  | succ ell ih =>
    apply (splitBits ell).injective
    change tensorLayout oneBit (clockLayout ell) (zeroBits (1+clockSize ell)) =
      splitBits ell (zeroBits (ell+1))
    rw [tensorLayout_zero,ih]
    rfl

lemma clockLocal_length_eq (ell : ℕ) (t : Bits ell) :
    (clockLocal ell t).length = (basisSequence ell t).length := by
  induction ell with
  | zero => rfl
  | succ ell ih =>
    change (tensorCircuit (if t 0 = 0 then ([] : Circuit elementary 1) else xCircuit)
      (clockLocal ell (fun i => t i.succ))).length = _
    rw [tensorCircuit_length,ih]
    simp only [basisSequence,List.length_map,tensorSequence_length]
    by_cases h : t 0 = 0 <;> simp [h,xCircuit]

lemma clockLocal_length (ell : ℕ) (t : Bits ell) : (clockLocal ell t).length ≤ ell := by
  rw [clockLocal_length_eq]
  exact basisSequence_length ell t

/-- All physical qubits of F: selector, clock, interleaved work pairs, ancillas. -/
def physicalSize (ell s r : ℕ) : ℕ := 1+(clockSize ell+(bellSize (s+1)+r))

lemma physicalSize_eq (ell s r : ℕ) : physicalSize ell s r =
    1+ell+2*(s+1)+r := by rw [physicalSize,clockSize_eq,bellSize_eq]; omega

def FLayout (ell s r : ℕ) : Basis (physicalSize ell s r) ≃ Small ell s r :=
  tensorLayout oneBit (tensorLayout (clockLayout ell)
    (tensorLayout (signedLayout s) (Equiv.refl (Bits r))))

/-- A physical circuit in the fixed H/X/Z/CNOT alphabet. -/
def physicalF (ell s r : ℕ) (t : Bits ell) : Circuit elementary (physicalSize ell s r) :=
  tensorCircuit xCircuit (tensorCircuit (clockLocal ell t)
    (tensorCircuit (signedLocal s) ([] : Circuit elementary r)))

/-- Full operator equality, stronger than matching the prepared state alone. -/
theorem physicalF_matrix (ell s r : ℕ) (t : Bits ell) : (physicalF ell s r t).matrix =
    (F ell s r t).submatrix (FLayout ell s r) (FLayout ell s r) := by
  unfold physicalF F FLayout
  apply tensorCircuit_matrix_of _ _ _ _ oneBit _ xCircuit_matrix
  apply tensorCircuit_matrix_of _ _ _ _ (clockLayout ell) _ (clockLocal_matrix ell t)
  apply tensorCircuit_matrix_of _ _ _ _ (signedLayout s) (Equiv.refl (Bits r))
    (signedLocal_matrix s)
  rfl

@[simp] lemma FLayout_zero (ell s r : ℕ) : FLayout ell s r
    (zeroBits (physicalSize ell s r)) = smallZero ell s r := by
  unfold FLayout physicalSize
  rw [tensorLayout_zero,tensorLayout_zero,tensorLayout_zero,clockLayout_zero,signedLayout_zero]
  rfl

/-- The native local circuit and the original matrix chronology have the same operator. -/
theorem physicalF_sequence_matrix (ell s r : ℕ) (t : Bits ell) :
    (physicalF ell s r t).matrix =
      (sequenceMatrix (FSequence ell s r t)).submatrix (FLayout ell s r) (FLayout ell s r) := by
  rw [FSequence_matrix]
  exact physicalF_matrix ell s r t

lemma physicalF_length_eq (ell s r : ℕ) (t : Bits ell) :
    (physicalF ell s r t).length = (FSequence ell s r t).length := by
  unfold physicalF
  rw [tensorCircuit_length,tensorCircuit_length,tensorCircuit_length]
  simp only [clockLocal_length_eq,signedLocal_length,List.length_nil,FSequence,
    tensorSequence_length,signedBellSequence_length]
  rfl

/-- The gate count is unchanged by adding actual wire-placement certificates. -/
theorem physicalF_length (ell s r : ℕ) (t : Bits ell) :
    (physicalF ell s r t).length ≤ ell+2*s+6 := by
  rw [physicalF_length_eq]
  exact FSequence_length ell s r t

/-- Running the native local-gate circuit on any density is exactly FρF†,
expressed using the physical coordinate layout. -/
theorem physicalF_run (ell s r : ℕ) (t : Bits ell) (ρ : Matrix (Small ell s r) _ ℂ) :
    (physicalF ell s r t).run (ρ.submatrix (FLayout ell s r) (FLayout ell s r)) =
      (OneCleanQubit.evolve (F ell s r t) ρ).submatrix (FLayout ell s r) (FLayout ell s r) := by
  rw [Circuit.run_eq_evolve,physicalF_matrix]
  exact evolve_submatrix _ _ _

/-- Equation (S4.Ex12) in the native physical local-gate model. -/
theorem physicalF_column (ell s r : ℕ) (t : Bits ell)
    (x : Basis (physicalSize ell s r)) :
    (physicalF ell s r t).matrix x (zeroBits (physicalSize ell s r)) =
      (if (FLayout ell s r x).1 = 1 then 1 else 0) *
        (if (FLayout ell s r x).2.1 = t then 1 else 0) *
          SourceBias.zVector (FLayout ell s r x).2.2.1 *
            (if (FLayout ell s r x).2.2.2 = zeroBits r then 1 else 0) := by
  rw [physicalF_matrix,Matrix.submatrix_apply,FLayout_zero]
  exact F_column ell s r t _

/-- The head/tail split of bit *positions*. -/
def splitPosition (s : ℕ) : Fin (s+1) ≃ (Fin 1 ⊕ Fin s) where
  toFun i := Fin.cases (Sum.inl 0) (fun j => Sum.inr j) i
  invFun p := Sum.elim (fun _ => 0) Fin.succ p
  left_inv i := by refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv p := by
    rcases p with i | i
    · fin_cases i; rfl
    · rfl

/-- The position permutation underlying `pairShuffle`, with head positions 0,1. -/
def pairPositions (s : ℕ) : (Fin (s+1) ⊕ Fin (s+1)) ≃
    (Fin 2 ⊕ (Fin s ⊕ Fin s)) :=
  ((splitPosition s).sumCongr (splitPosition s)).trans
    ((Equiv.sumSumSumComm (Fin 1) (Fin s) (Fin 1) (Fin s)).trans
      (finSumFinEquiv.sumCongr (Equiv.refl (Fin s ⊕ Fin s))))

/-- Explicit bijection from each copy's work-qubit positions to physical positions. -/
def bellWire : (s : ℕ) → (Fin s ⊕ Fin s) ≃ Fin (bellSize s)
  | 0 => {
      toFun := Sum.elim Fin.elim0 Fin.elim0
      invFun := Fin.elim0
      left_inv := by intro p; rcases p with i | i <;> exact Fin.elim0 i
      right_inv := by intro i; exact Fin.elim0 i }
  | s+1 => (pairPositions s).trans
      (((Equiv.refl (Fin 2)).sumCongr (bellWire s)).trans finSumFinEquiv)

/-- `bellLayout` reads each coordinate from exactly the physical position named
by `bellWire`; hence it is a wire permutation, not an arbitrary basis permutation. -/
theorem bellLayout_induced (s : ℕ) (x : Basis (bellSize s)) (j : Fin s ⊕ Fin s) :
    Sum.elim (bellLayout s x).1 (bellLayout s x).2 j = x (bellWire s j) := by
  induction s with
  | zero => rcases j with i | i <;> exact Fin.elim0 i
  | succ s ih =>
    rcases j with j | j
    · refine Fin.cases ?_ (fun i => ?_) j
      · rfl
      · change (bellLayout s (fun j => x (Fin.natAdd 2 j))).1 i =
          x (Fin.natAdd 2 (bellWire s (Sum.inl i)))
        exact ih _ (Sum.inl i)
    · refine Fin.cases ?_ (fun i => ?_) j
      · rfl
      · change (bellLayout s (fun j => x (Fin.natAdd 2 j))).2 i =
          x (Fin.natAdd 2 (bellWire s (Sum.inr i)))
        exact ih _ (Sum.inr i)

def clockWire : (ell : ℕ) → Fin ell ≃ Fin (clockSize ell)
  | 0 => Equiv.refl _
  | ell+1 => (splitPosition ell).trans
      (((Equiv.refl (Fin 1)).sumCongr (clockWire ell)).trans finSumFinEquiv)

theorem clockLayout_induced (ell : ℕ) (x : Basis (clockSize ell)) (j : Fin ell) :
    clockLayout ell x j = x (clockWire ell j) := by
  induction ell with
  | zero => exact Fin.elim0 j
  | succ ell ih =>
    refine Fin.cases ?_ (fun i => ?_) j
    · rfl
    · change clockLayout ell (fun j => x (Fin.natAdd 1 j)) i =
        x (Fin.natAdd 1 (clockWire ell i))
      exact ih _ i

/-- Canonical bit coordinates of the two grouped work registers. -/
def workPairRead (s : ℕ) (p : WorkSpace s × WorkSpace s) :
    (Fin (s+1) ⊕ Fin (s+1)) → QBit :=
  Sum.elim ((splitBits s).symm p.1) ((splitBits s).symm p.2)

theorem signedLayout_induced (s : ℕ) (x : Basis (bellSize (s+1)))
    (j : Fin (s+1) ⊕ Fin (s+1)) :
    workPairRead s (signedLayout s x) j = x (bellWire (s+1) j) := by
  simpa [workPairRead,signedLayout,workPairBasis] using bellLayout_induced (s+1) x j

/-- Tensor a pair of permutations of physical positions. -/
def tensorWire {p q : ℕ} {a b : Type*} (u : a ≃ Fin p) (v : b ≃ Fin q) :
    (a ⊕ b) ≃ Fin (p+q) := (u.sumCongr v).trans finSumFinEquiv

def prodRead {a b p q : Type*} (u : a → p → QBit) (v : b → q → QBit)
    (x : a × b) : p ⊕ q → QBit := Sum.elim (u x.1) (v x.2)

lemma tensorLayout_induced {p q : ℕ} {a b i j : Type*}
    (e : Basis p ≃ a) (f : Basis q ≃ b) (u : a → i → QBit) (v : b → j → QBit)
    (wu : i ≃ Fin p) (wv : j ≃ Fin q)
    (he : ∀ x z, u (e x) z = x (wu z)) (hf : ∀ x z, v (f x) z = x (wv z))
    (x : Basis (p+q)) (z : i ⊕ j) :
    prodRead u v (tensorLayout e f x) z = x (tensorWire wu wv z) := by
  rcases z with z | z
  · exact he _ z
  · exact hf _ z

abbrev FPositions (ell s r : ℕ) :=
  Fin 1 ⊕ (Fin ell ⊕ ((Fin (s+1) ⊕ Fin (s+1)) ⊕ Fin r))

def FRead (ell s r : ℕ) : Small ell s r → FPositions ell s r → QBit :=
  prodRead (fun b _ => b) (prodRead (fun c => c) (prodRead (workPairRead s) (fun a => a)))

def FWire (ell s r : ℕ) : FPositions ell s r ≃ Fin (physicalSize ell s r) :=
  tensorWire (Equiv.refl (Fin 1)) (tensorWire (clockWire ell)
    (tensorWire (bellWire (s+1)) (Equiv.refl (Fin r))))

/-- The full coordinate equivalence used by the physical preparation is induced
by the explicitly constructed bijection `FWire` of qubit positions. -/
theorem FLayout_induced (ell s r : ℕ) (x : Basis (physicalSize ell s r))
    (j : FPositions ell s r) :
    FRead ell s r (FLayout ell s r x) j = x (FWire ell s r j) := by
  unfold FRead FLayout FWire
  apply tensorLayout_induced
  · intro y i
    fin_cases i
    rfl
  · intro y j
    apply tensorLayout_induced
    · exact clockLayout_induced ell
    · intro z k
      apply tensorLayout_induced
      · exact signedLayout_induced s
      · intro a i
        rfl

end Paper25.StatePreparationLocal
