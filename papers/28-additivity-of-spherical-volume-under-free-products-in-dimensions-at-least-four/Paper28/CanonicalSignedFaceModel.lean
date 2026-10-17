import Paper28.SignedCoordinateFaceModel

/-! Every valid signed coordinate face is exactly its coordinate set
with the unique signs inherited from any containing cross-polytope face.
This identifies arbitrary carrier orbit representatives with signed-by-A
cells, for which quotient injectivity and local roundness are proved. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open scoped Classical
variable {G : Type*} [Group G] [DecidableEq G]

def positiveSignedCoordinates (F : Finset (SignedCoordinate G)) : Finset G :=
  (F.filter (fun s => s.2 = true)).image Prod.fst

theorem signedCoordinateEmbedding_in_face (F : Finset (SignedCoordinate G))
    (hF : ∀ g, ¬((g,true) ∈ F ∧ (g,false) ∈ F)) (v : SignedCoordinate G) (hv : v ∈ F) :
    signedCoordinateEmbedding (positiveSignedCoordinates F) v.1 = v := by
  obtain ⟨g,b⟩ := v
  cases b
  · have hn : g ∉ positiveSignedCoordinates F := by
      intro h
      obtain ⟨w,hw,hwg⟩ := Finset.mem_image.mp h
      obtain ⟨hwF,hwT⟩ := Finset.mem_filter.mp hw
      have he : w = (g,true) := Prod.ext hwg hwT
      exact hF g ⟨he ▸ hwF,hv⟩
    simp [signedCoordinateEmbedding,hn]
  · have hp : g ∈ positiveSignedCoordinates F :=
      Finset.mem_image.mpr ⟨(g,true),Finset.mem_filter.mpr ⟨hv,rfl⟩,rfl⟩
    simp [signedCoordinateEmbedding,hp]

theorem signedCoordinateFace_of_subface (F P : Finset (SignedCoordinate G))
    (hF : ∀ g, ¬((g,true) ∈ F ∧ (g,false) ∈ F)) (hPF : P ⊆ F) :
    signedCoordinateFace (positiveSignedCoordinates F) (P.image Prod.fst) = P := by
  apply Finset.ext
  intro v
  constructor
  · intro hv
    obtain ⟨g,hg,rfl⟩ := Finset.mem_map.mp hv
    obtain ⟨w,hw,hwg⟩ := Finset.mem_image.mp hg
    rw [← hwg,signedCoordinateEmbedding_in_face F hF w (hPF hw)]
    exact hw
  · intro hv
    apply Finset.mem_map.mpr
    exact ⟨v.1,Finset.mem_image.mpr ⟨v,hv,rfl⟩,signedCoordinateEmbedding_in_face F hF v (hPF hv)⟩

def coordinateChainProjection (C : Finset (Finset (SignedCoordinate G))) : Finset (Finset G) :=
  C.image (fun F => F.image Prod.fst)

theorem coordinate_cell_has_canonical_signed_model (families : Finset (Finset G))
    (C : Finset (Finset (SignedCoordinate G))) (hC : CoordinateBarycentricCell families C) :
    ∃ A : Finset G, signedCoordinateFaceChain A (coordinateChainProjection C) = C := by
  obtain ⟨F,hF,hMax⟩ := finite_face_chain_has_maximum C hC.1 hC.2.1
  refine ⟨positiveSignedCoordinates F,?_⟩
  apply Finset.ext
  intro P
  constructor
  · intro hP
    obtain ⟨E,hE,hEP⟩ := Finset.mem_image.mp hP
    obtain ⟨D,hD,hDE⟩ := Finset.mem_image.mp hE
    have he : signedCoordinateFace (positiveSignedCoordinates F) (D.image Prod.fst) = D :=
      signedCoordinateFace_of_subface F D (hC.2.2 F hF).2.1 (hMax D hD)
    rw [← hDE,he] at hEP
    exact hEP ▸ hD
  · intro hP
    apply Finset.mem_image.mpr
    refine ⟨P.image Prod.fst,Finset.mem_image.mpr ⟨P,hP,rfl⟩,?_⟩
    exact signedCoordinateFace_of_subface F P (hC.2.2 F hF).2.1 (hMax P hP)

end Paper28
