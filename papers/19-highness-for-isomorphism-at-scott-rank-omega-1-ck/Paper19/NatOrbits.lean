import Paper19.NatSyntax
import Paper19.NatIsomorphism
import Paper19.EffectiveSyntax

namespace Paper19
open Infinitary

def NatTupleOrbit (M : NatModel) {m : ℕ} (a b : Fin m → ℕ) : Prop :=
  ∃ f : NatIso M M, ∀ i, f.map (a i)=b i

def natTupleEnv (M : NatModel) {m : ℕ} (b : Fin m → ℕ) : ℕ → ℕ :=
  fun i => if hi : i<m then b ⟨i,hi⟩ else M.zero

theorem nat_tuple_orbit_iff (T : Tree) (tag : Bool) {m : ℕ} (a b : Fin m → Carrier T) :
    NatTupleOrbit (natModel T tag) (fun i => carrierEquivNat T (a i))
      (fun i => carrierEquivNat T (b i)) ↔ ActualTupleOrbit T tag a b := by
  constructor
  · rintro ⟨f,hf⟩
    refine ⟨f.toCarrier,fun i => ?_⟩
    change (carrierEquivNat T).symm (f.map (carrierEquivNat T (a i))) = b i
    rw [hf i,Equiv.symm_apply_apply]
  · rintro ⟨f,hf⟩
    refine ⟨f.toNatIso,fun i => ?_⟩
    change carrierEquivNat T (f.map ((carrierEquivNat T).symm (carrierEquivNat T (a i)))) = _
    rw [Equiv.symm_apply_apply,hf i]

theorem nat_tuple_formula_transfer (T : Tree) (tag : Bool) {m : ℕ} (b : Fin m → Carrier T) (φ : Formula) :
    φ.RealizeNat (natModel T tag) (natTupleEnv (natModel T tag) (fun i => carrierEquivNat T (b i))) ↔
      φ.Realize tag (tupleEnv b) := by
  have he : natTupleEnv (natModel T tag) (fun i => carrierEquivNat T (b i)) =
      fun i => carrierEquivNat T (tupleEnv b i) := by
    funext i
    by_cases hi : i<m <;> simp [natTupleEnv,tupleEnv,hi]
  rw [he]
  exact formula_nat_transfer T tag (tupleEnv b) φ

/-- All Nat-presented finite tuple orbits, including mixed and empty tuples. -/
theorem all_nat_tuple_orbits (T : Tree) (hT : ComputablePred T.mem) (tag : Bool)
    (m : ℕ) (a : Fin m → ℕ) :
    ∃ φ : Formula, ComputablyPresented φ ∧ ∀ b : Fin m → ℕ,
      φ.RealizeNat (natModel T tag) (natTupleEnv (natModel T tag) b) ↔
        NatTupleOrbit (natModel T tag) a b := by
  let ac := fun i => (carrierEquivNat T).symm (a i)
  obtain ⟨φ,hφ,ha⟩ := all_tuple_orbits hT tag m ac
  refine ⟨φ,hφ,fun b => ?_⟩
  let bc := fun i => (carrierEquivNat T).symm (b i)
  have hea : (fun i => carrierEquivNat T (ac i)) = a := by funext i; exact Equiv.apply_symm_apply _ _
  have heb : (fun i => carrierEquivNat T (bc i)) = b := by funext i; exact Equiv.apply_symm_apply _ _
  have hh := (nat_tuple_formula_transfer T tag bc φ).trans
    ((ha bc).trans (nat_tuple_orbit_iff T tag ac bc).symm)
  simpa only [hea,heb] using hh

end Paper19
