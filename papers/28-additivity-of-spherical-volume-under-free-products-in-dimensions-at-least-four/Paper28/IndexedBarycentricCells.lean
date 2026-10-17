import Paper28.SignedBarycentricRoundCharts
import Paper28.BarycentricChainIndependence
import Paper28.SignedFaceGeometry
import Paper28.SphericalSimplexPatch

/-! Actual ordered barycentric simplices are tied to their face-chain
coordinate cells, including zero boundary weights and positive interior
weights. Their linear independence and finite support are native. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
open scoped Classical
variable {G : Type*} [Group G] [DecidableEq G] {k : ℕ}

def indexedChainFaces (σ : Fin (k+1) → Finset G) : Finset (Finset G) := Finset.univ.image σ

def indexedChainCoefficients (σ : Fin (k+1) → Finset G) (t : stdSimplex ℝ (Fin (k+1))) (F : Finset G) : ℝ :=
  ∑ i, if σ i = F then t.val i else 0

theorem indexedChainCoefficients_at (σ : Fin (k+1) → Finset G) (hσ : Function.Injective σ)
    (t : stdSimplex ℝ (Fin (k+1))) (i : Fin (k+1)) : indexedChainCoefficients σ t (σ i) = t.val i := by
  simp [indexedChainCoefficients,hσ.eq_iff]

theorem indexedChainCoefficients_nonneg (σ : Fin (k+1) → Finset G)
    (t : stdSimplex ℝ (Fin (k+1))) : ∀ F, 0 ≤ indexedChainCoefficients σ t F := by
  intro F
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact t.property.1 i
  · exact le_rfl

theorem indexedChain_raw_eq (A : Finset G) (σ : Fin (k+1) → Finset G) (hσ : Function.Injective σ)
    (t : stdSimplex ℝ (Fin (k+1))) :
    signedChainRaw A (indexedChainFaces σ) (indexedChainCoefficients σ t) =
      sphericalBarycentricVector (fun i => signedFaceCenter A (σ i)) t := by
  unfold signedChainRaw indexedChainFaces sphericalBarycentricVector
  rw [Finset.sum_image (fun i _ j _ he => hσ he)]
  simp_rw [indexedChainCoefficients_at σ hσ]

theorem indexedChain_closed_cell (A : Finset G) (σ : Fin (k+1) → Finset G) (hσ : Function.Injective σ) :
    {u : RegularSphere G | u.val ∈ sphericalSimplexPatch (fun i => signedFaceCenter A (σ i))} ⊆
      closedSignedBarycentricCell A (indexedChainFaces σ) := by
  intro u hu
  obtain ⟨t,ht⟩ := hu
  refine ⟨indexedChainCoefficients σ t,fun F _ => indexedChainCoefficients_nonneg σ t F,?_⟩
  rw [signedChainPoint,indexedChain_raw_eq A σ hσ]
  exact ht.symm

theorem indexedChain_strict_cell (A : Finset G) (σ : Fin (k+1) → Finset G) (hσ : Function.Injective σ)
    (t : stdSimplex ℝ (Fin (k+1))) (ht : ∀ i, 0 < t.val i) (u : RegularSphere G)
    (hu : u.val = sphericalNormalize (sphericalBarycentricVector (fun i => signedFaceCenter A (σ i)) t)) :
    u ∈ strictSignedBarycentricCell A (indexedChainFaces σ) := by
  refine ⟨indexedChainCoefficients σ t,?_,?_⟩
  · intro F hF
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hF
    rw [indexedChainCoefficients_at σ hσ]
    exact ht i
  · rw [signedChainPoint,indexedChain_raw_eq A σ hσ]
    exact hu

theorem indexedChain_chain (σ : Fin (k+1) → Finset G)
    (hChain : ∀ i j, σ i ⊆ σ j ∨ σ j ⊆ σ i) :
    ∀ F ∈ indexedChainFaces σ, ∀ E ∈ indexedChainFaces σ, F ⊆ E ∨ E ⊆ F := by
  rintro F hF E hE
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hF
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hE
  exact hChain i j

theorem indexedChain_faces_nonempty (σ : Fin (k+1) → Finset G) (hFaces : ∀ i, (σ i).Nonempty) :
    ∀ F ∈ indexedChainFaces σ, F.Nonempty := by
  intro F hF
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hF
  exact hFaces i

theorem indexedChain_centers_linearIndependent (A : Finset G) (σ : Fin (k+1) → Finset G)
    (hσ : Function.Injective σ) (hFaces : ∀ i, (σ i).Nonempty)
    (hChain : ∀ i j, σ i ⊆ σ j ∨ σ j ⊆ σ i) :
    LinearIndependent ℝ (fun i => signedFaceCenter A (σ i)) := by
  let e : Fin (k+1) → indexedChainFaces σ := fun i => ⟨σ i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
  have he : Function.Injective e := by
    intro i j hij
    exact hσ (congrArg Subtype.val hij)
  exact (signed_barycentric_centers_linearIndependent A (indexedChainFaces σ)
    (indexedChain_chain σ hChain) (indexedChain_faces_nonempty σ hFaces)).comp e he

end Paper28
