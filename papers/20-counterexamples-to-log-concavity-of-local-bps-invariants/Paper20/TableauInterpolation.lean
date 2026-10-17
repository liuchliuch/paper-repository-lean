import Paper20.PresentedMurphy
import Paper20.TableauSpectralSeparation

namespace Paper20.Seminormal
open Paper20.YoungShapes Paper20.PresentedHecke
noncomputable section
set_option maxHeartbeats 6000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

lemma exists_separating_index {n : ℕ} (t s : AllFilling n) (h : t≠s) :
    ∃ i : Fin n, allContent t i≠allContent s i := by
  by_contra hn
  apply h
  apply allContent_injective n
  funext i
  by_contra hi
  exact hn ⟨i,hi⟩

def separatingIndex {n : ℕ} (t s : AllFilling n) (h : t≠s) : Fin n :=
  Classical.choose (exists_separating_index t s h)

lemma separatingIndex_ne {n : ℕ} (t s : AllFilling n) (h : t≠s) :
    allContent t (separatingIndex t s h)≠allContent s (separatingIndex t s h) :=
  Classical.choose_spec (exists_separating_index t s h)

abbrev Others {n : ℕ} (t : AllFilling n) := {s : AllFilling n // s≠t}

section Field
variable {F : Type*} [Field F]

def allEigenvalue (v : F) {n : ℕ} (t : AllFilling n) (i : Fin n) : F := v^(2*allContent t i)

lemma separating_difference_ne_zero (v : F) (hp : Function.Injective (fun d : ℤ => v^d))
    {n : ℕ} (t : AllFilling n) (s : Others t) :
    allEigenvalue v t (separatingIndex t s.val (fun h => s.property h.symm))-
      allEigenvalue v s.val (separatingIndex t s.val (fun h => s.property h.symm))≠0 := by
  apply sub_ne_zero.mpr
  intro he
  have hc := hp he
  apply separatingIndex_ne t s.val (fun h => s.property h.symm)
  omega

/-- A genuine Lagrange factor made from an actual Murphy element in the
honest Hecke algebra, with the quantum eigenvalue differences as scalars. -/
def interpolationFactor (v : F) {n : ℕ} (t : AllFilling n) (s : Others t) :
    Presented F n (v-v⁻¹) :=
  let i := separatingIndex t s.val (fun h => s.property h.symm)
  (allEigenvalue v t i-allEigenvalue v s.val i)⁻¹ •
    (murphyElement F n (v-v⁻¹) i.val i.isLt-algebraMap F _ (allEigenvalue v s.val i))

def factorCoefficient (v : F) {n : ℕ} (t : AllFilling n) (s : Others t) (b : AllFilling n) : F :=
  let i := separatingIndex t s.val (fun h => s.property h.symm)
  (allEigenvalue v t i-allEigenvalue v s.val i)⁻¹*(allEigenvalue v b i-allEigenvalue v s.val i)

lemma interpolationFactor_apply (v : F) (hv : v≠0)
    (hp : Function.Injective (fun d : ℤ => v^d)) {n : ℕ}
    (t : AllFilling n) (s : Others t) (μ : Shape n) (f : StandardFilling μ → F) (b : StandardFilling μ) :
    (blockRepresentation v hv hp μ (interpolationFactor v t s) f) b=
      factorCoefficient v t s ⟨μ,b⟩*f b := by
  unfold interpolationFactor
  dsimp only
  rw [map_smul,map_sub,blockRepresentation_murphy,AlgHom.commutes]
  let i := separatingIndex t s.val (fun h => s.property h.symm)
  change (allEigenvalue v t i-allEigenvalue v s.val i)⁻¹*
    (eigenvalue v b i*f b-allEigenvalue v s.val i*f b)=factorCoefficient v t s ⟨μ,b⟩*f b
  unfold factorCoefficient
  change (allEigenvalue v t i-allEigenvalue v s.val i)⁻¹*
    (eigenvalue v b i*f b-allEigenvalue v s.val i*f b)=
      ((allEigenvalue v t i-allEigenvalue v s.val i)⁻¹*
        (eigenvalue v b i-allEigenvalue v s.val i))*f b
  ring

lemma interpolationList_apply (v : F) (hv : v≠0)
    (hp : Function.Injective (fun d : ℤ => v^d)) {n : ℕ}
    (t : AllFilling n) (ss : List (Others t)) (μ : Shape n)
    (f : StandardFilling μ → F) (b : StandardFilling μ) :
    (blockRepresentation v hv hp μ ((ss.map (interpolationFactor v t)).prod) f) b=
      (ss.map (fun s => factorCoefficient v t s ⟨μ,b⟩)).prod*f b := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
    rw [List.map_cons,List.prod_cons,map_mul]
    change (blockRepresentation v hv hp μ (interpolationFactor v t s)
      (blockRepresentation v hv hp μ ((ss.map (interpolationFactor v t)).prod) f)) b=_
    rw [interpolationFactor_apply,ih]
    simp only [List.map_cons,List.prod_cons,mul_assoc]

/-- An actual ordered product of genuine Murphy Lagrange factors,
constructed in the honest Hecke algebra rather than in its target matrices. -/
def tableauProjector (v : F) {n : ℕ} (t : AllFilling n) : Presented F n (v-v⁻¹) :=
  (((Finset.univ:Finset (Others t)).toList).map (interpolationFactor v t)).prod

/-- The actual algebra element projects onto precisely the selected
actual standard-tableau coordinate across every actual shape block. -/
theorem tableauProjector_apply (v : F) (hv : v≠0)
    (hp : Function.Injective (fun d : ℤ => v^d)) {n : ℕ}
    (t : AllFilling n) (μ : Shape n) (f : StandardFilling μ → F) (b : StandardFilling μ) :
    (blockRepresentation v hv hp μ (tableauProjector v t) f) b=
      if (⟨μ,b⟩:AllFilling n)=t then f b else 0 := by
  rw [tableauProjector,interpolationList_apply]
  by_cases ht : (⟨μ,b⟩:AllFilling n)=t
  · rw [if_pos ht]
    have hprod : (((Finset.univ:Finset (Others t)).toList).map
        (fun s => factorCoefficient v t s ⟨μ,b⟩)).prod=1 := by
      apply List.prod_eq_one
      intro x hx
      obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hx
      unfold factorCoefficient
      rw [ht]
      exact inv_mul_cancel₀ (separating_difference_ne_zero v hp t s)
    rw [hprod,one_mul]
  · rw [if_neg ht]
    let s : Others t := ⟨⟨μ,b⟩,ht⟩
    have hs : s ∈ (Finset.univ:Finset (Others t)).toList := by simp
    have hz : factorCoefficient v t s ⟨μ,b⟩=0 := by
      unfold factorCoefficient
      dsimp only [s]
      rw [sub_self,mul_zero]
    have hm : (0:F) ∈ (((Finset.univ:Finset (Others t)).toList).map
        (fun s => factorCoefficient v t s ⟨μ,b⟩)) := List.mem_map.mpr ⟨s,hs,hz⟩
    rw [List.prod_eq_zero_iff.mpr hm,zero_mul]

end Field
end
end Paper20.Seminormal
