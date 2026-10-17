import Paper28.CoordinateBarycentricCover
import Paper28.CoordinateBarycentricOrbits

/-! The signed-coordinate face-chain model and the actual signed-by-A
barycentric vectors are exactly the same geometric objects. This connects
native coordinate-sphere coverage with the explicit finite orbit seeds. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open scoped Classical
variable {G : Type*} [Group G] [DecidableEq G]

def signedCoordinateEmbedding (A : Finset G) : G ↪ SignedCoordinate G where
  toFun g := (g,decide (g ∈ A))
  inj' _ _ h := congrArg Prod.fst h

def signedCoordinateFace (A F : Finset G) : Finset (SignedCoordinate G) := F.map (signedCoordinateEmbedding A)

theorem signedCoordinateFace_fst (A F : Finset G) : (signedCoordinateFace A F).image Prod.fst = F := by
  apply Finset.ext
  intro g
  constructor
  · intro hg
    obtain ⟨v,hv,hvg⟩ := Finset.mem_image.mp hg
    obtain ⟨x,hx,hxv⟩ := Finset.mem_map.mp hv
    have he : x = g := (congrArg Prod.fst hxv).trans hvg
    exact he ▸ hx
  · intro hg
    exact Finset.mem_image.mpr ⟨signedCoordinateEmbedding A g,Finset.mem_map.mpr ⟨g,hg,rfl⟩,rfl⟩

theorem signedCoordinateFace_injective (A : Finset G) : Function.Injective (signedCoordinateFace A) := by
  intro F E he
  have hh := congrArg (fun Q : Finset (SignedCoordinate G) => Q.image Prod.fst) he
  simpa only [signedCoordinateFace_fst] using hh

theorem signedCoordinateFace_mono (A F E : Finset G) (hFE : F ⊆ E) :
    signedCoordinateFace A F ⊆ signedCoordinateFace A E := by
  intro v hv
  obtain ⟨g,hg,rfl⟩ := Finset.mem_map.mp hv
  exact Finset.mem_map.mpr ⟨g,hFE hg,rfl⟩

theorem signedCoordinateFace_no_opposites (A F : Finset G) :
    ∀ g, ¬((g,true) ∈ signedCoordinateFace A F ∧ (g,false) ∈ signedCoordinateFace A F) := by
  rintro g ⟨hT,hF⟩
  obtain ⟨x,_,hx⟩ := Finset.mem_map.mp hT
  obtain ⟨y,_,hy⟩ := Finset.mem_map.mp hF
  have hxy : x = y := (congrArg Prod.fst hx).trans (congrArg Prod.fst hy).symm
  subst y
  have hh := congrArg Prod.snd (hx.symm.trans hy)
  exact Bool.noConfusion hh

theorem signedCoordinateFace_cross_face (A F : Finset G) (families : Finset (Finset G))
    (hF : F.Nonempty) (γ : G) (E : Finset G) (hE : E ∈ families)
    (hFE : F ⊆ E.image (fun g => γ*g)) : CoordinateCrossFace families (signedCoordinateFace A F) := by
  refine ⟨hF.map,signedCoordinateFace_no_opposites A F,γ,E,hE,?_⟩
  rw [signedCoordinateFace_fst]
  exact hFE

theorem coordinateFaceBarycenter_signed (A F : Finset G) :
    coordinateFaceBarycenter (signedCoordinateFace A F) = signedFaceCenter A F := by
  unfold coordinateFaceBarycenter signedFaceCenter signedFaceVector signedCoordinateFace
  apply congrArg sphericalNormalize
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro g _
  simp [signedCoordinateVector,signedCoordinateEmbedding,coordinateSign]

def signedCoordinateFaceChain (A : Finset G) (C : Finset (Finset G)) : Finset (Finset (SignedCoordinate G)) :=
  C.image (signedCoordinateFace A)

theorem signedCoordinateFaceChain_cell (A F : Finset G) (C : Finset (Finset G))
    (families : Finset (Finset G)) (hC : C.Nonempty)
    (hFaces : ∀ E ∈ C, E.Nonempty ∧ E ⊆ F)
    (hChain : ∀ E ∈ C, ∀ D ∈ C, E ⊆ D ∨ D ⊆ E)
    (γ : G) (E : Finset G) (hE : E ∈ families) (hFE : F ⊆ E.image (fun g => γ*g)) :
    CoordinateBarycentricCell families (signedCoordinateFaceChain A C) := by
  refine ⟨hC.image _,?_,?_⟩
  · intro P hP Q hQ
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨D,hD,rfl⟩ := Finset.mem_image.mp hQ
    exact (hChain B hB D hD).imp (signedCoordinateFace_mono A B D) (signedCoordinateFace_mono A D B)
  · intro P hP
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hP
    exact signedCoordinateFace_cross_face A B families (hFaces B hB).1 γ E hE ((hFaces B hB).2.trans hFE)

end Paper28
