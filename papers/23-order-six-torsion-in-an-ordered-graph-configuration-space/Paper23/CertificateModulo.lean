import Paper23.CertificateCocycleSoundness

/-! Modular sparse normalization, justified by coefficientwise reduction of the
actual original-coordinate integer chain. -/
namespace Paper23.CertificateChecks
open Cubical

abbrev ModRawChain := RawCube →₀ ZMod 6

noncomputable def reduceChain : RawChain →ₗ[ℤ] ModRawChain :=
  Finsupp.mapRange.linearMap modSix

@[simp] theorem reduceChain_apply (x : RawChain) (c : RawCube) :
    reduceChain x c = modSix (x c) := rfl

theorem modulo_smul (a : ℤ) (x : ModRawChain) : (a % 6) • x = a • x := by
  ext c
  simp only [Finsupp.smul_apply,zsmul_eq_mul]
  exact congrArg (fun z : ZMod 6 => z * x c) (ZMod.intCast_mod a 6)

/-- Canonical coefficient residues, with zero entries deleted. -/
def reduceEntries (xs : List (ℕ × ℤ)) : List (ℕ × ℤ) :=
  List.rec [] (fun p _ rec =>
    if p.2 % 6 = 0 then rec else (p.1,p.2 % 6) :: rec) xs

theorem reduceEntries_sound (xs : List (ℕ × ℤ)) :
    reduceChain (codeChain (reduceEntries xs)) = reduceChain (codeChain xs) := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    simp only [reduceEntries] at ih
    by_cases h : p.2 % 6 = 0
    · simp only [reduceEntries,if_pos h]
      rw [ih,codeChain_cons,map_add,map_smul]
      have hz : p.2 • reduceChain (basis (decodeCube p.1)) = 0 := by
        rw [← modulo_smul p.2,h,zero_smul]
      rw [hz,zero_add]
    · simp only [reduceEntries,if_neg h,codeChain_cons,map_add,map_smul,ih]
      rw [modulo_smul]

def modularMerge (xs ys : List (ℕ × ℤ)) : List (ℕ × ℤ) := reduceEntries (merge xs ys)

theorem modularMerge_sound (xs ys : List (ℕ × ℤ)) :
    reduceChain (codeChain (modularMerge xs ys)) =
      reduceChain (codeChain xs) + reduceChain (codeChain ys) := by
  rw [modularMerge,reduceEntries_sound,codeChain_merge,map_add]

def modularMergePass (xs : List (List (ℕ × ℤ))) : List (List (ℕ × ℤ)) :=
  (List.rec (motive := fun _ => List (List (ℕ × ℤ)) × List (List (ℕ × ℤ)))
    ([],[])
    (fun a tail state =>
      ((match tail with | [] => [a] | b :: _ => modularMerge a b :: state.2),state.1)) xs).1

noncomputable def modChunkChain (xss : List (List (ℕ × ℤ))) : ModRawChain :=
  (xss.map fun xs => reduceChain (codeChain xs)).sum

theorem modChunkChain_modularMergePass (xss : List (List (ℕ × ℤ))) :
    modChunkChain (modularMergePass xss) = modChunkChain xss := by
  induction xss using List.twoStepInduction with
  | nil => rfl
  | singleton a => rfl
  | cons_cons a b rest ih _ =>
    change reduceChain (codeChain (modularMerge a b)) + modChunkChain (modularMergePass rest) =
      reduceChain (codeChain a) + (reduceChain (codeChain b) + modChunkChain rest)
    rw [modularMerge_sound,ih]
    abel

def modularCollapse (fuel : ℕ) (xs : List (List (ℕ × ℤ))) : List (List (ℕ × ℤ)) :=
  Nat.rec (motive := fun _ => List (List (ℕ × ℤ)) → List (List (ℕ × ℤ)))
    (fun xs => xs)
    (fun _ rec xs => match xs with
      | [] => []
      | [xs] => [reduceEntries xs]
      | xs => rec (modularMergePass xs)) fuel xs

theorem modChunkChain_modularCollapse (fuel : ℕ) (xss : List (List (ℕ × ℤ))) :
    modChunkChain (modularCollapse fuel xss) = modChunkChain xss := by
  induction fuel generalizing xss with
  | zero => rfl
  | succ fuel ih =>
    match xss with
    | [] => rfl
    | [xs] => simp [modularCollapse,modChunkChain,reduceEntries_sound]
    | a :: b :: rest =>
      change modChunkChain (modularCollapse fuel (modularMergePass (a :: b :: rest))) = _
      rw [ih,modChunkChain_modularMergePass]

theorem modChunkChain_singletons (xs : List (ℕ × ℤ)) :
    modChunkChain (xs.map (fun p => [p])) = reduceChain (codeChain xs) := by
  induction xs with
  | nil => simp [modChunkChain]
  | cons p xs ih =>
    simp only [List.map_cons,modChunkChain,List.sum_cons,codeChain_cons,
      codeChain_nil,map_add,map_smul,map_zero,add_zero] at ih ⊢
    rw [ih]

theorem modularNormalization_sound (fuel : ℕ) (xs ys : List (ℕ × ℤ))
    (checked : modularCollapse fuel (xs.map (fun p => [p])) = [ys]) :
    reduceChain (codeChain ys) = reduceChain (codeChain xs) := by
  have h := modChunkChain_modularCollapse fuel (xs.map (fun p => [p]))
  rw [checked,modChunkChain_singletons] at h
  simpa [modChunkChain] using h

/-- The modular sparse check yields the cocycle on all original three-chains. -/
theorem cocycle_of_modular_transpose
    (checked : reduceChain (restrictCubes 3 (coBoundary phiVector)) = 0)
    (x : RawChain) (hx : x ∈ Chains 3) : phi (boundary x) = 0 := by
  apply cocycle_of_projected_transpose ?_ x hx
  intro d
  have h := congrArg (fun y : ModRawChain => y d) checked
  simpa only [reduceChain_apply,Finsupp.zero_apply] using h

end Paper23.CertificateChecks
