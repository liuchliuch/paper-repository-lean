import Paper23.Cubical
import Paper23.CertificateData
import Mathlib.Data.ZMod.Basic

/-! Interpretation of the exported certificate in the actual labelled
cubical chains. No disjointness or degree property is built into the decoder;
these are separate proof obligations on every term of the chain. -/
namespace Paper23.CertificateChecks
open Cubical CertificateData

/-- Tokens 0..31 encode vertices; tokens 32..70 encode moving graph edges. -/
def decodeCell (n : ℕ) : GraphCell :=
  if h : n < 32 then .vertex ⟨n, h⟩ else .edge ⟨(n-32) % 39, Nat.mod_lt _ (by decide)⟩

def encodeCell : GraphCell → ℕ
  | .vertex v => v.val
  | .edge e => 32 + e.val

/-- Four tokens retain the order of the four particle labels. -/
def decodeCube (n : ℕ) : RawCube :=
  [decodeCell (n / 357911 % 71), decodeCell (n / 5041 % 71),
   decodeCell (n / 71 % 71), decodeCell (n % 71)]

def encodeCube (c : RawCube) : ℕ := c.foldl (fun n a => 71*n + encodeCell a) 0

@[simp] theorem decodeCell_encodeCell (a : GraphCell) : decodeCell (encodeCell a) = a := by
  cases a with
  | vertex v => simp [encodeCell, decodeCell, v.isLt]
  | edge e =>
    have h : ¬ 32 + e.val < 32 := by omega
    simp [encodeCell, decodeCell, h, Nat.mod_eq_of_lt e.isLt]

theorem encodeCell_lt (a : GraphCell) : encodeCell a < 71 := by
  cases a with
  | vertex v => have := v.isLt; dsimp [encodeCell]; omega
  | edge e => have := e.isLt; dsimp [encodeCell]; omega

/-- The packing is faithful on four graph-cell lists. -/
theorem decodeCube_encodeCube (c : RawCube) (hlen : c.length = 4) :
    decodeCube (encodeCube c) = c := by
  obtain ⟨a,b,c,d,rfl⟩ := List.length_eq_four.mp hlen
  have ha := encodeCell_lt a
  have hb := encodeCell_lt b
  have hc := encodeCell_lt c
  have hd := encodeCell_lt d
  simp only [encodeCube, List.foldl_cons, List.foldl_nil, Nat.mul_zero, Nat.zero_add]
  unfold decodeCube
  have h0 : (71 * (71 * (71 * encodeCell a + encodeCell b) + encodeCell c) + encodeCell d) /
      357911 % 71 = encodeCell a := by omega
  have h1 : (71 * (71 * (71 * encodeCell a + encodeCell b) + encodeCell c) + encodeCell d) /
      5041 % 71 = encodeCell b := by omega
  have h2 : (71 * (71 * (71 * encodeCell a + encodeCell b) + encodeCell c) + encodeCell d) /
      71 % 71 = encodeCell c := by omega
  have h3 : (71 * (71 * (71 * encodeCell a + encodeCell b) + encodeCell c) + encodeCell d) %
      71 = encodeCell d := by omega
  rw [h0, h1, h2, h3]
  simp

/-- The cochain is defined on the actual labelled cubes, not on an unrelated
list of precomputed evaluations. Outside the explicit sparse table it is zero. -/
noncomputable def phiValue (c : RawCube) : ℤ := lookup phiTable (encodeCube c)

noncomputable def phi : RawChain →ₗ[ℤ] ZMod 6 :=
  Finsupp.linearCombination ℤ (fun c => (phiValue c : ZMod 6))

@[simp] theorem phi_basis (c : RawCube) : phi (basis c) = (phiValue c : ZMod 6) := by
  simp [phi, basis]

/-- The exported integer coefficients are interpreted as a genuine Finsupp
chain in the original oriented basis. -/
noncomputable def codeChain (xs : List (ℕ × ℤ)) : RawChain :=
  (xs.map fun p => p.2 • basis (decodeCube p.1)).sum

/-- This expression computes the actual cochain on the decoded cube, including
both the particle labels and the graph-cell decoder. -/
noncomputable def codeEvaluation (xs : List (ℕ × ℤ)) : ℤ :=
  (xs.map fun p => p.2 * phiValue (decodeCube p.1)).sum

@[simp] theorem codeChain_nil : codeChain [] = 0 := rfl
@[simp] theorem codeChain_cons (p : ℕ × ℤ) (xs : List (ℕ × ℤ)) :
    codeChain (p :: xs) = p.2 • basis (decodeCube p.1) + codeChain xs := rfl

theorem codeChain_append (xs ys : List (ℕ × ℤ)) :
    codeChain (xs ++ ys) = codeChain xs + codeChain ys := by
  simp [codeChain]

theorem codeChain_flatMap {α : Type*} (xs : List α) (f : α → List (ℕ × ℤ)) :
    codeChain (xs.flatMap f) = (xs.map (fun x => codeChain (f x))).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [List.flatMap_cons, codeChain_append, ih]

/-- The numerical computation is connected to the Finsupp linear map. -/
theorem phi_codeChain (xs : List (ℕ × ℤ)) :
    phi (codeChain xs) = (codeEvaluation xs : ZMod 6) := by
  induction xs with
  | nil => simp [codeEvaluation]
  | cons p xs ih =>
    simp only [codeChain_cons, map_add, map_smul, phi_basis, ih]
    simp [codeEvaluation, Int.cast_add, Int.cast_mul]

/-- The full chain is the sum of the bounded data chunks. -/
noncomputable def z : RawChain := (zChunks.map codeChain).sum

/-- The integer computation before reduction modulo six. -/
noncomputable def zEvaluation : ℤ := (zChunks.map codeEvaluation).sum

theorem phi_z_eq_evaluation : phi z = (zEvaluation : ZMod 6) := by
  simp only [z, map_list_sum, List.map_map, Function.comp_def, phi_codeChain, zEvaluation]
  simp only [Int.cast_list_sum, List.map_map, Function.comp_def]

/-- Validity is checked on the actual graph endpoint closure sets. -/
def validDegreeTwo (n : ℕ) : Prop := IsCube (decodeCube n) ∧ degree (decodeCube n) = 2

instance (n : ℕ) : Decidable (validDegreeTwo n) := by
  unfold validDegreeTwo IsCube
  infer_instance

/-- A finite valid list of terms gives a chain in the degree-two subcomplex. -/
theorem codeChain_mem (xs : List (ℕ × ℤ))
    (h : ∀ p ∈ xs, validDegreeTwo p.1) : codeChain xs ∈ Chains 2 := by
  induction xs with
  | nil => exact (Chains 2).zero_mem
  | cons p xs ih =>
    rw [codeChain_cons]
    apply (Chains 2).add_mem
    · apply (Chains 2).smul_mem
      exact Finsupp.single_mem_supported ℤ 1 (h p (by simp))
    · apply ih
      intro p hp
      exact h p (by simp [hp])

end Paper23.CertificateChecks
