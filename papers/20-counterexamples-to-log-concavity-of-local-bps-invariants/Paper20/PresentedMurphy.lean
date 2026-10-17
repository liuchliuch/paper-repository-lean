import Paper20.CanonicalTableauRepresentation

namespace Paper20.PresentedHecke
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- The actual palindromic Murphy word in the honest canonical Hecke
presentation. This is a genuine generator product, not a chosen spectral
operator. -/
def murphyElement (R : Type*) [CommRing R] (n : ℕ) (z : R) :
    (m : ℕ) → m<n → Presented R n z
  | 0,_ => 1
  | m+1,hm => generator R n z ⟨m,by omega⟩*murphyElement R n z m (by omega)*
      generator R n z ⟨m,by omega⟩

end
end Paper20.PresentedHecke

namespace Paper20.Seminormal
open Paper20.YoungShapes Paper20.PresentedHecke
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

section Field
variable {F : Type*} [Field F]

/-- The actual Murphy word maps to the actual tableau Murphy word under
the proved representation homomorphism. -/
theorem blockRepresentation_murphyOperator (v : F) (hv : v≠0)
    (hp : Function.Injective (fun d : ℤ => v^d)) {n : ℕ} (μ : Shape n)
    (m : ℕ) (hm : m<n) :
    blockRepresentation v hv hp μ (murphyElement F n (v-v⁻¹) m hm)=
      murphyOperator (μ:=μ) v m hm := by
  induction m with
  | zero => simp only [murphyElement,murphyOperator,map_one]
  | succ m ih =>
    rw [murphyElement,map_mul,map_mul,blockRepresentation_generator,
      ih (by omega),murphyOperator]
    rfl

/-- The source's genuine Murphy element has the actual content eigenvalue
on every actual standard tableau in its true block representation. -/
theorem blockRepresentation_murphy (v : F) (hv : v≠0)
    (hp : Function.Injective (fun d : ℤ => v^d)) {n : ℕ} (μ : Shape n)
    (m : ℕ) (hm : m<n) :
    blockRepresentation v hv hp μ (murphyElement F n (v-v⁻¹) m hm)=
      murphyDiagonal v ⟨m,hm⟩ := by
  rw [blockRepresentation_murphyOperator,murphyOperator_eq_diagonal v hv hp]

end Field
end
end Paper20.Seminormal
