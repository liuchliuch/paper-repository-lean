import Verification.SourceSupportGeometry
import Verification.SourceConsequences
import Verification.QuantitativeDisk
import Verification.Example24Full
import Paper17.EuclideanCombination

/-! Explicit additional source contracts. These supplement the original
sixteen fixed contracts; no extra geometric conclusion is assumed. -/
noncomputable section
open scoped Topology Pointwise BigOperators

namespace P17Contract.SourceContract

theorem positive_body_support_convex :
    ∀ (n : ℕ),
    Convex ℝ (Set.range (@bodySphericalSupport n)) := @P17Contract.positive_body_support_convex

end P17Contract.SourceContract

namespace Paper17.SourceContract

theorem supportFunction_minkowski :
    ∀ {n : ℕ} {K L : Set (V n)}
    (hK : IsCompact K) (hneK : K.Nonempty) (hL : IsCompact L) (hneL : L.Nonempty)
    (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (u : V n),
    supportFunction (α • K + β • L) u
      = α * supportFunction K u + β * supportFunction L u := @Paper17.supportFunction_minkowski

end Paper17.SourceContract

namespace P17Contract.SourceContract

theorem normalFan_add_sets :
    ∀ {n : ℕ} (K L : Set (V n)),
    normalFan (K + L) = (fun p : Set (V n) × Set (V n) => p.1 ∩ p.2) ''
      (normalFan K ×ˢ normalFan L) := @P17Contract.normalFan_add_sets

end P17Contract.SourceContract

namespace P17Contract.SourceContract

theorem normalFan_smul_sets :
    ∀ {n : ℕ} (K : Set (V n)) {t : ℝ} (ht : 0 < t),
    normalFan (t • K) = normalFan K := @P17Contract.normalFan_smul_sets

end P17Contract.SourceContract

namespace P17Contract.SourceContract

theorem euclideanHausdorffDist_eq_norm_sphericalSupport :
    ∀ {n : ℕ} (K L : PosBody n),
    euclideanHausdorffDist K.carrier L.carrier =
      ‖bodySphericalSupport K - bodySphericalSupport L‖ := @P17Contract.euclideanHausdorffDist_eq_norm_sphericalSupport

end P17Contract.SourceContract

namespace Paper17.EuclideanSupport.SourceContract

theorem hausdorffDist_minkowskiComb_le_max :
    ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {K : Set E}
    (hK : IsCompact K) (hneK : K.Nonempty) (hconvK : Convex ℝ K)
    (ι : Type*) (s : Finset ι) (w : ι → ℝ) (P : ι → Set E)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1)
    (hP : ∀ i ∈ s, IsCompact (P i) ∧ (P i).Nonempty)
    {δ : ℝ} (hδ : ∀ i ∈ s, Metric.hausdorffDist (P i) K ≤ δ),
    Metric.hausdorffDist ((∑ i ∈ s, (w i) • (P i : Set E) : Set E)) K ≤ δ := @Paper17.EuclideanSupport.hausdorffDist_minkowskiComb_le_max

end Paper17.EuclideanSupport.SourceContract

namespace Paper17.EuclideanSupport.SourceContract

theorem equation_2_2_full :
    ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {K : Set E}
    (hK : IsCompact K) (hneK : K.Nonempty) (hconvK : Convex ℝ K)
    (ι : Type*) (s : Finset ι) (w : ι → ℝ) (P : ι → Set E)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1)
    (hP : ∀ i ∈ s, IsCompact (P i) ∧ (P i).Nonempty),
    ∃ j ∈ s, (∀ i ∈ s, Metric.hausdorffDist (P i) K ≤ Metric.hausdorffDist (P j) K) ∧
      Metric.hausdorffDist ((∑ i ∈ s, w i • (P i : Set E) : Set E)) K ≤
        ∑ i ∈ s, w i * Metric.hausdorffDist (P i) K ∧
      (∑ i ∈ s, w i * Metric.hausdorffDist (P i) K) ≤ Metric.hausdorffDist (P j) K := @Paper17.EuclideanSupport.equation_2_2_full

end Paper17.EuclideanSupport.SourceContract

namespace Paper17.SourceContract

theorem common_refinement_of_rational_normal :
    ∀ {n m : ℕ} (Ps : Fin m → Polytope n)
    (hPs : ∀ i, HasRationalNormalPresentation (Ps i)),
    ∃ Q : DelzantPolytope n, ∀ i, (NormalFan Q.val).refines (NormalFan (Ps i)) := @Paper17.common_refinement_of_rational_normal

end Paper17.SourceContract

namespace P17Contract.SourceContract

theorem theorem_1_2_euclidean :
    ∀ (n : ℕ),
    IsAbsoluteExtensor (EuclideanDelzantSpace n) ∧ IsAbsoluteRetract (EuclideanDelzantSpace n) := @P17Contract.theorem_1_2_euclidean

end P17Contract.SourceContract

namespace P17Contract.SourceContract

theorem theorem_1_2_euclidean_open :
    ∀ {n : ℕ} (W : Set (PaperSupportSpace n))
    (hW : IsOpen W) (hcW : Convex ℝ W)
    (hne : Nonempty {P : EuclideanDelzantSpace n // bodySphericalSupport P.val.body ∈ W}),
    IsAbsoluteExtensor {P : EuclideanDelzantSpace n // bodySphericalSupport P.val.body ∈ W} ∧
      IsAbsoluteRetract {P : EuclideanDelzantSpace n // bodySphericalSupport P.val.body ∈ W} := @P17Contract.theorem_1_2_euclidean_open

end P17Contract.SourceContract

namespace P17Contract.SourceContract

theorem euclidean_extension_in_spherical_open_controlled :
    ∀ {n : ℕ}
    (W : Set (PaperSupportSpace n)) (hW : IsOpen W) (hcW : Convex ℝ W)
    (hne : ∃ P : EuclideanDelzantSpace n, bodySphericalSupport P.val.body ∈ W)
    (X : Type) [MetricSpace X] (A : Set X) (hA : IsClosed A)
    (f : A → EuclideanDelzantSpace n) (hf : Continuous f)
    (hfW : ∀ a, bodySphericalSupport (f a).val.body ∈ W),
    ∃ F : X → EuclideanDelzantSpace n, Continuous F ∧ (∀ a : A, F a = f a) ∧
      (∀ x, bodySphericalSupport (F x).val.body ∈ W) ∧
      LocallyFiniteFansOn (fun x => (euclideanDelzantHomeomorph n).symm (F x)) Aᶜ := @P17Contract.euclidean_extension_in_spherical_open_controlled

end P17Contract.SourceContract

namespace P17Contract.SourceContract

theorem euclidean_open_ball_absoluteExtensor_retract :
    ∀ {n : ℕ} (P : EuclideanDelzantSpace n)
    {r : ℝ} (hr : 0 < r),
    IsAbsoluteExtensor (Metric.ball P r) ∧ IsAbsoluteRetract (Metric.ball P r) := @P17Contract.euclidean_open_ball_absoluteExtensor_retract

end P17Contract.SourceContract

namespace P17Contract.SourceContract

theorem lemma_4_2_euclidean :
    ∀ {n m : ℕ} (K : EuclideanBody n)
    (Ps : Fin m → EuclideanDelzantSpace n) {η : ℝ} (hη : 0 < η),
    ∃ Q : EuclideanDelzantSpace n, dist Q.val K < η ∧
      ∀ i, DelzantPolytope.le ((euclideanDelzantHomeomorph n).symm (Ps i))
        ((euclideanDelzantHomeomorph n).symm Q) := @P17Contract.lemma_4_2_euclidean

end P17Contract.SourceContract

namespace P17Contract.SourceContract

theorem proposition_4_3_euclidean :
    ∀ {X : Type} [MetricSpace X] {n : ℕ}
    (f : X → EuclideanBody n) (hf : Continuous f)
    (ε : X → ℝ) (hε : Continuous ε) (hpos : ∀ x, 0 < ε x),
    ∃ g : X → EuclideanDelzantSpace n, Continuous g ∧
      (∀ x, dist (g x).val (f x) < ε x) ∧
      LocallyFiniteFansOn (fun x => (⟨(g x).val.body, (g x).property⟩ : DelzantSpace n)) Set.univ := @P17Contract.proposition_4_3_euclidean

end P17Contract.SourceContract

namespace P17Contract.SourceContract

theorem theorem_4_4_euclidean :
    ∀ (n : ℕ),
    ∃ H : EuclideanBody n × ℝ → EuclideanBody n, Continuous H ∧
      (∀ K, H (K, 0) = K) ∧
      (∀ K t, 0 < t → t ≤ 1 →
        ∃ P : EuclideanDelzantSpace n, H (K, t) = P.val ∧ dist (H (K, t)) K < t) := @P17Contract.theorem_4_4_euclidean

end P17Contract.SourceContract

namespace P17Contract.SourceContract

theorem corollary_1_3_euclidean :
    ∀ {n : ℕ} (hn : 1 ≤ n) (P : EuclideanDelzantSpace n),
    ∃ H : EuclideanDelzantSpace n × ℝ → EuclideanDelzantSpace n, Continuous H ∧
      (∀ Q, H (Q, 0) = Q) ∧ (∀ Q, H (Q, 1) = P) ∧ (∀ t, H (P, t) = P) := @P17Contract.corollary_1_3_euclidean

end P17Contract.SourceContract

namespace P17Contract.SourceContract

theorem euclidean_homotopyGroup_eq_one :
    ∀ {n : ℕ} (hn : 1 ≤ n)
    (P : EuclideanDelzantSpace n) (k : ℕ),
    ∀ a : HomotopyGroup.Pi (k + 1) (EuclideanDelzantSpace n) P, a = 1 := @P17Contract.euclidean_homotopyGroup_eq_one

end P17Contract.SourceContract

namespace P17Contract.SourceContract

theorem euclidean_sphere_filling_in_spherical_open :
    ∀ {n : ℕ}
    (W : Set (PaperSupportSpace n)) (hW : IsOpen W) (hcW : Convex ℝ W)
    (hne : ∃ P : EuclideanDelzantSpace n, bodySphericalSupport P.val.body ∈ W)
    (k : ℕ) (f : sphere k → EuclideanDelzantSpace n) (hf : Continuous f)
    (hfW : ∀ x, bodySphericalSupport (f x).val.body ∈ W),
    ∃ F : ball k → EuclideanDelzantSpace n, Continuous F ∧
      (∀ x : sphere k, F ⟨x.val, x.property.le⟩ = f x) ∧
      (∀ x, bodySphericalSupport (F x).val.body ∈ W) ∧
      (∀ C : Set (ball k), IsCompact C → (∀ x ∈ C, ∑ i, x.val i ^ 2 < 1) →
        ((fun x => normalFan (F x).val.body.carrier) '' C).Finite) := @P17Contract.euclidean_sphere_filling_in_spherical_open

end P17Contract.SourceContract

namespace P17Contract.SourceContract

theorem euclidean_sphere_filling_in_open_ball :
    ∀ {n : ℕ} (P : EuclideanDelzantSpace n)
    {r : ℝ} (hr : 0 < r) (k : ℕ) (f : sphere k → EuclideanDelzantSpace n)
    (hf : Continuous f) (hfr : ∀ x, dist (f x) P < r),
    ∃ F : ball k → EuclideanDelzantSpace n, Continuous F ∧
      (∀ x : sphere k, F ⟨x.val, x.property.le⟩ = f x) ∧ (∀ x, dist (F x) P < r) ∧
      (∀ C : Set (ball k), IsCompact C → (∀ x ∈ C, ∑ i, x.val i ^ 2 < 1) →
        ((fun x => normalFan (F x).val.body.carrier) '' C).Finite) := @P17Contract.euclidean_sphere_filling_in_open_ball

end P17Contract.SourceContract

namespace P17Contract.SourceContract

theorem prop_2_5_euclidean :
    ∀ {n : ℕ} (K : EuclideanBody n) (L : ℕ → EuclideanBody n),
    Filter.Tendsto (fun j => euclideanHausdorffDist K.body.carrier (L j).body.carrier)
      Filter.atTop (𝓝 0) ↔
    Filter.Tendsto (fun j => volSymmDiff K.body.carrier (L j).body.carrier) Filter.atTop (𝓝 0) := @P17Contract.prop_2_5_euclidean

end P17Contract.SourceContract

namespace P17Contract.SourceContract

theorem theorem_1_2_volume :
    ∀ (n : ℕ),
    IsAbsoluteExtensor (VolumeDelzantSpace n) ∧ IsAbsoluteRetract (VolumeDelzantSpace n) := @P17Contract.theorem_1_2_volume

end P17Contract.SourceContract

namespace P17Contract.SourceContract

theorem theorem_1_2_volume_open :
    ∀ {n : ℕ} (W : Set (PaperSupportSpace n))
    (hW : IsOpen W) (hcW : Convex ℝ W)
    (hne : Nonempty {P : VolumeDelzantSpace n // bodySphericalSupport P.val.body.body ∈ W}),
    IsAbsoluteExtensor {P : VolumeDelzantSpace n // bodySphericalSupport P.val.body.body ∈ W} ∧
      IsAbsoluteRetract {P : VolumeDelzantSpace n // bodySphericalSupport P.val.body.body ∈ W} := @P17Contract.theorem_1_2_volume_open

end P17Contract.SourceContract

namespace P17Contract.SourceContract

theorem volume_extension_in_spherical_open_controlled :
    ∀ {n : ℕ}
    (W : Set (PaperSupportSpace n)) (hW : IsOpen W) (hcW : Convex ℝ W)
    (hne : ∃ P : VolumeDelzantSpace n, bodySphericalSupport P.val.body.body ∈ W)
    (X : Type) [MetricSpace X] (A : Set X) (hA : IsClosed A)
    (f : A → VolumeDelzantSpace n) (hf : Continuous f)
    (hfW : ∀ a, bodySphericalSupport (f a).val.body.body ∈ W),
    ∃ F : X → VolumeDelzantSpace n, Continuous F ∧ (∀ a : A, F a = f a) ∧
      (∀ x, bodySphericalSupport (F x).val.body.body ∈ W) ∧
      (∀ x ∈ Aᶜ, ∃ U ∈ 𝓝 x,
        ((fun y => normalFan (F y).val.body.body.carrier) '' U).Finite) := @P17Contract.volume_extension_in_spherical_open_controlled

end P17Contract.SourceContract

namespace P17Contract.SourceContract

theorem lemma_2_3_euclidean_open :
    ∀ {n m : ℕ} (P : EuclideanDelzantSpace n)
    (Ps : Fin m → EuclideanDelzantSpace n) {η : ℝ} (hη : 0 < η)
    (W : Set (PaperSupportSpace n)) (hW : IsOpen W)
    (hP : bodySphericalSupport P.val.body ∈ W),
    ∃ Q : EuclideanDelzantSpace n, dist Q P < η ∧
      bodySphericalSupport Q.val.body ∈ W ∧
      DelzantPolytope.le ((euclideanDelzantHomeomorph n).symm P)
        ((euclideanDelzantHomeomorph n).symm Q) ∧
      ∀ i, DelzantPolytope.le ((euclideanDelzantHomeomorph n).symm (Ps i))
        ((euclideanDelzantHomeomorph n).symm Q) := @P17Contract.lemma_2_3_euclidean_open

end P17Contract.SourceContract

namespace P17Contract.SourceContract

theorem euclidean_locally_contractible :
    ∀ {n : ℕ} (P : EuclideanDelzantSpace n)
    (U : Set (EuclideanDelzantSpace n)) (hU : U ∈ 𝓝 P),
    ∃ V : Set (EuclideanDelzantSpace n), IsOpen V ∧ P ∈ V ∧ V ⊆ U ∧
      ∃ H : V × ℝ → EuclideanDelzantSpace n, Continuous H ∧
        (∀ y : V, H (y, 0) = y.val) ∧ (∀ y : V, H (y, 1) = P) ∧
        (∀ y t, H (y, t) ∈ U) ∧ (∀ t, ∀ hp : P ∈ V, H (⟨P, hp⟩, t) = P) := @P17Contract.euclidean_locally_contractible

end P17Contract.SourceContract

namespace P17Contract.SourceContract

theorem euclidean_contractible :
    ∀ {n : ℕ} (hn : 1 ≤ n) (P : EuclideanDelzantSpace n),
    ContractibleSpace (EuclideanDelzantSpace n) := @P17Contract.euclidean_contractible

end P17Contract.SourceContract

namespace P17Contract.SourceContract

theorem euclidean_pathConnected :
    ∀ {n : ℕ} (hn : 1 ≤ n) (P : EuclideanDelzantSpace n),
    PathConnectedSpace (EuclideanDelzantSpace n) := @P17Contract.euclidean_pathConnected

end P17Contract.SourceContract

namespace P17Contract.SourceContract

theorem corollary_1_3_volume :
    ∀ {n : ℕ} (hn : 1 ≤ n) (P : VolumeDelzantSpace n),
    ∃ H : VolumeDelzantSpace n × ℝ → VolumeDelzantSpace n, Continuous H ∧
      (∀ Q, H (Q, 0) = Q) ∧ (∀ Q, H (Q, 1) = P) ∧ (∀ t, H (P, t) = P) := @P17Contract.corollary_1_3_volume

end P17Contract.SourceContract

namespace P17Contract.SourceContract

theorem volume_homotopyGroup_eq_one :
    ∀ {n : ℕ} (hn : 1 ≤ n)
    (P : VolumeDelzantSpace n) (k : ℕ),
    ∀ a : HomotopyGroup.Pi (k + 1) (VolumeDelzantSpace n) P, a = 1 := @P17Contract.volume_homotopyGroup_eq_one

end P17Contract.SourceContract

namespace P17Contract.SourceContract

theorem volume_contractible :
    ∀ {n : ℕ} (hn : 1 ≤ n) (P : VolumeDelzantSpace n),
    ContractibleSpace (VolumeDelzantSpace n) := @P17Contract.volume_contractible

end P17Contract.SourceContract

namespace P17Contract.SourceContract

theorem volume_pathConnected :
    ∀ {n : ℕ} (hn : 1 ≤ n) (P : VolumeDelzantSpace n),
    PathConnectedSpace (VolumeDelzantSpace n) := @P17Contract.volume_pathConnected

end P17Contract.SourceContract

namespace P17Contract.SourceContract

theorem volume_locally_contractible :
    ∀ {n : ℕ} (P : VolumeDelzantSpace n)
    (U : Set (VolumeDelzantSpace n)) (hU : U ∈ 𝓝 P),
    ∃ V : Set (VolumeDelzantSpace n), IsOpen V ∧ P ∈ V ∧ V ⊆ U ∧
      ∃ H : V × ℝ → VolumeDelzantSpace n, Continuous H ∧
        (∀ y : V, H (y, 0) = y.val) ∧ (∀ y : V, H (y, 1) = P) ∧
        (∀ y t, H (y, t) ∈ U) ∧ (∀ t, ∀ hp : P ∈ V, H (⟨P, hp⟩, t) = P) := @P17Contract.volume_locally_contractible

end P17Contract.SourceContract

namespace P17Contract.SourceContract

theorem volume_sphere_filling_in_spherical_open :
    ∀ {n : ℕ}
    (W : Set (PaperSupportSpace n)) (hW : IsOpen W) (hcW : Convex ℝ W)
    (hne : ∃ P : VolumeDelzantSpace n, bodySphericalSupport P.val.body.body ∈ W)
    (k : ℕ) (f : sphere k → VolumeDelzantSpace n) (hf : Continuous f)
    (hfW : ∀ x, bodySphericalSupport (f x).val.body.body ∈ W),
    ∃ F : ball k → VolumeDelzantSpace n, Continuous F ∧
      (∀ x : sphere k, F ⟨x.val, x.property.le⟩ = f x) ∧
      (∀ x, bodySphericalSupport (F x).val.body.body ∈ W) ∧
      (∀ C : Set (ball k), IsCompact C → (∀ x ∈ C, ∑ i, x.val i ^ 2 < 1) →
        ((fun x => normalFan (F x).val.body.body.carrier) '' C).Finite) := @P17Contract.volume_sphere_filling_in_spherical_open

end P17Contract.SourceContract

namespace Paper17.Example24.SourceContract

theorem raysSum_integral_primitive :
    ∀ (i : Fin 5),
    raysSum i = realRays (fun _ : Unit => raysSumZ i) () ∧
      Int.gcd (raysSumZ i 0) (raysSumZ i 1) = 1 := @Paper17.Example24.raysSum_integral_primitive

end Paper17.Example24.SourceContract

namespace Paper17.Example24.SourceContract

theorem pentagon_consecutive_determinants :
    ∀ (i : Fin 5),
    det2 (pentagonBasis i 0) (pentagonBasis i 1) = if i = 2 then 2 else 1 := @Paper17.Example24.pentagon_consecutive_determinants

end Paper17.Example24.SourceContract

namespace Paper17.Example24.SourceContract

theorem source_example_2_4 :
    IsDelzant (triangle 1) ∧ IsDelzant (triangle (-1)) ∧
      ¬ IsDelzant ((triangle 1).add (triangle (-1))) ∧
      Fan.Equivalent (NormalFan ((triangle 1).add (triangle (-1)))) (NormalFan pentagon) ∧
      (∀ i, Int.gcd (raysSumZ i 0) (raysSumZ i 1) = 1) ∧
      IsDelzant (prism (triangle 1) 1) ∧ IsDelzant (prism (triangle (-1)) 1) ∧
      ¬ IsDelzant ((prism (triangle 1) 1).add (prism (triangle (-1)) 1)) ∧
      IsDelzant hexagon ∧
      (∀ x : V 2, x ∈ hexagon.carrier ↔ -2 ≤ x 0 ∧ x 0 ≤ 2 ∧ -2 ≤ x 1 ∧
        x 1 ≤ 2 ∧ x 0 + x 1 ≤ 3 ∧ -x 0 + x 1 ≤ 3) ∧
      IsDelzant exampleS ∧
      (NormalFan exampleS).refines (NormalFan (prism (triangle 1) 1)) ∧
      (NormalFan exampleS).refines (NormalFan (prism (triangle (-1)) 1)) ∧
      (∀ x ∈ exampleS.carrier, ‖P17Contract.euclideanCoordinates 3 x‖ ≤ 3) ∧
      ‖P17Contract.euclideanCoordinates 3 (prismPoint (vec2 2 (-2)) 1)‖ = 3 ∧
      (∀ t : ℝ, 0 < t →
        IsDelzant ((prism (triangle 1) 1).add (exampleS.smul t)) ∧
        (NormalFan ((prism (triangle 1) 1).add (exampleS.smul t))).refines
          (NormalFan (prism (triangle 1) 1)) ∧
        (NormalFan ((prism (triangle 1) 1).add (exampleS.smul t))).refines
          (NormalFan (prism (triangle (-1)) 1)) ∧
        P17Contract.euclideanHausdorffDist ((prism (triangle 1) 1).add (exampleS.smul t)).carrier
          (prism (triangle 1) 1).carrier = 3 * t) := @Paper17.Example24.source_example_2_4

end Paper17.Example24.SourceContract

namespace Paper17.Example24.SourceContract

theorem triangle_sum_five_ray_fan :
    Fan.Equivalent (NormalFan ((triangle 1).add (triangle (-1)))) (NormalFan pentagon) ∧
      ∀ i, (normalConeAt ((triangle 1).add (triangle (-1))) (pentagonVertex i) : Set (V 2)) =
        {u | ∃ c : Fin 2 → ℝ, (∀ j, 0 ≤ c j) ∧ u = ∑ j, c j • pentagonBasis i j} := @Paper17.Example24.triangle_sum_five_ray_fan

end Paper17.Example24.SourceContract

namespace Paper17.Example24.SourceContract

theorem hexagon_normalCone :
    ∀ (i : Fin 6),
    (normalConeAt hexagon (hexagonVertex i) : Set (V 2)) =
      {u | ∃ c : Fin 2 → ℝ, (∀ j, 0 ≤ c j) ∧ u = ∑ j, c j • hexagonBasis i j} := @Paper17.Example24.hexagon_normalCone

end Paper17.Example24.SourceContract

namespace Paper17.Example24.SourceContract

theorem mem_prism_carrier :
    ∀ (P : Polytope 2) {a : ℝ} (ha : 0 < a) (x : V 3),
    x ∈ (prism P a).carrier ↔ planeProjection x ∈ P.carrier ∧ 0 ≤ x 2 ∧ x 2 ≤ a := @Paper17.Example24.mem_prism_carrier

end Paper17.Example24.SourceContract

namespace Paper17.Example24.SourceContract

theorem normal_prism_endpoint :
    ∀ (P : Polytope 2) {a : ℝ} (ha : 0 < a)
    {p : V 2} (hp : p ∈ P.verts) (b : Bool) (u : V 3),
    u ∈ normalConeAt (prism P a) (prismPoint p (if b then a else 0)) ↔
      planeProjection u ∈ normalConeAt P p ∧ (if b then 0 ≤ u 2 else u 2 ≤ 0) := @Paper17.Example24.normal_prism_endpoint

end Paper17.Example24.SourceContract

namespace Paper17.Example24.SourceContract

theorem example24_exact_euclidean_error :
    ∀ (P : Polytope 3) {t : ℝ} (ht : 0 < t),
    P17Contract.euclideanHausdorffDist (P.add (exampleS.smul t)).carrier P.carrier = 3 * t := @Paper17.Example24.example24_exact_euclidean_error

end Paper17.Example24.SourceContract

namespace P17Contract.QuantitativeDisk.SourceContract

theorem quantitative_disk_filling :
    ∀ {n : ℕ} (f : Angle → EuclideanDelzantSpace n) (hf : Continuous f),
    ∃ F : ClosedDisk → EuclideanDelzantSpace n, Continuous F ∧
      (∀ θ, F (boundaryPoint θ) = f θ) ∧
      (∀ θ s (hs : 0 < s) (hsHalf : s ≤ 1 / 2),
        dist (F (polarClosed θ s hs.le (by linarith))) (f θ) ≤
          2 * s + Paper17.loopModulus f (s / 2)) ∧
      (∀ θ k s (hk : 1 ≤ k) (hlo : dyadicDepth (k + 1) ≤ s) (hhi : s ≤ dyadicDepth k),
        dist (F (annulusPoint θ k s hk hlo hhi)) (f θ) ≤
          dyadicDepth k + Paper17.loopModulus f (1 / (dyadicCount k : ℝ)) ∧
        dyadicDepth k + Paper17.loopModulus f (1 / (dyadicCount k : ℝ)) ≤
          2 * s + Paper17.loopModulus f (s / 2)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ θ s (hs : 0 < s) (hsHalf : s ≤ 1 / 2), s < δ →
          dist (F (polarClosed θ s hs.le (by linarith))) (f θ) < ε) ∧
      (∀ C : Set ClosedDisk, IsCompact C → (∀ x ∈ C, ‖x.val‖ < 1) →
        ((fun x => normalFan (F x).val.body.carrier) '' C).Finite) := @P17Contract.QuantitativeDisk.quantitative_disk_filling

end P17Contract.QuantitativeDisk.SourceContract

namespace Paper17.SourceContract

theorem loopModulus_tendsto_zero :
    ∀ {Θ Z : Type*} [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MetricSpace Z] {f : Θ → Z} (hf : Continuous f),
    Filter.Tendsto (loopModulus f) (𝓝[>] (0 : ℝ)) (𝓝 0) := @Paper17.loopModulus_tendsto_zero

end Paper17.SourceContract
