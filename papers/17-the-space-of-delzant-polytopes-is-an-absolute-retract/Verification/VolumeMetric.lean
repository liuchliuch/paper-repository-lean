import Verification.VolumeGeometry
import Verification.EuclideanApplications

noncomputable section
open scoped Topology
namespace P17Contract

/-- The main theorem with the literal volume-of-symmetric-difference metric. -/
theorem theorem_1_2_volume (n : ℕ) :
    IsAbsoluteExtensor (VolumeDelzantSpace n) ∧ IsAbsoluteRetract (VolumeDelzantSpace n) := by
  have hAE := absoluteExtensor_homeomorph (theorem_1_2_euclidean n).1 (volumeDelzantHomeomorph n)
  obtain ⟨P⟩ := Paper17.delzant_nonempty n
  exact ⟨hAE, def_1_1 hAE
    ⟨volumeDelzantHomeomorph n (euclideanDelzantHomeomorph n (ofProduction P))⟩⟩

/-- The support-open restriction is an AE and AR for the literal volume metric. -/
theorem theorem_1_2_volume_open {n : ℕ} (W : Set (PaperSupportSpace n))
    (hW : IsOpen W) (hcW : Convex ℝ W)
    (hne : Nonempty {P : VolumeDelzantSpace n // bodySphericalSupport P.val.body.body ∈ W}) :
    IsAbsoluteExtensor {P : VolumeDelzantSpace n // bodySphericalSupport P.val.body.body ∈ W} ∧
      IsAbsoluteRetract {P : VolumeDelzantSpace n // bodySphericalSupport P.val.body.body ∈ W} := by
  let e := volumeDelzantHomeomorph n
  let eW : {P : EuclideanDelzantSpace n // bodySphericalSupport P.val.body ∈ W} ≃ₜ
      {P : VolumeDelzantSpace n // bodySphericalSupport P.val.body.body ∈ W} :=
    { toFun := fun P => ⟨e P.val, P.property⟩
      invFun := fun P => ⟨e.symm P.val, P.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _ }
  have hneE : Nonempty {P : EuclideanDelzantSpace n // bodySphericalSupport P.val.body ∈ W} :=
    ⟨eW.symm (Classical.choice hne)⟩
  have hAE := absoluteExtensor_homeomorph (theorem_1_2_euclidean_open W hW hcW hneE).1 eW
  exact ⟨hAE, def_1_1 hAE hne⟩

/-- The locally finite fan conclusion is retained by the actual volume-metric
extension in every source open convex support set. -/
theorem volume_extension_in_spherical_open_controlled {n : ℕ}
    (W : Set (PaperSupportSpace n)) (hW : IsOpen W) (hcW : Convex ℝ W)
    (hne : ∃ P : VolumeDelzantSpace n, bodySphericalSupport P.val.body.body ∈ W)
    (X : Type) [MetricSpace X] (A : Set X) (hA : IsClosed A)
    (f : A → VolumeDelzantSpace n) (hf : Continuous f)
    (hfW : ∀ a, bodySphericalSupport (f a).val.body.body ∈ W) :
    ∃ F : X → VolumeDelzantSpace n, Continuous F ∧ (∀ a : A, F a = f a) ∧
      (∀ x, bodySphericalSupport (F x).val.body.body ∈ W) ∧
      (∀ x ∈ Aᶜ, ∃ U ∈ 𝓝 x,
        ((fun y => normalFan (F y).val.body.body.carrier) '' U).Finite) := by
  let e := volumeDelzantHomeomorph n
  obtain ⟨P, hP⟩ := hne
  obtain ⟨G, hGc, hGeq, hGW, hfin⟩ := euclidean_extension_in_spherical_open_controlled
    W hW hcW ⟨e.symm P, hP⟩ X A hA (e.symm ∘ f) (e.symm.continuous.comp hf) hfW
  refine ⟨e ∘ G, e.continuous.comp hGc, ?_, hGW, ?_⟩
  · intro a
    rw [Function.comp_apply, hGeq, Function.comp_apply, e.apply_symm_apply]
  · exact hfin

end P17Contract
