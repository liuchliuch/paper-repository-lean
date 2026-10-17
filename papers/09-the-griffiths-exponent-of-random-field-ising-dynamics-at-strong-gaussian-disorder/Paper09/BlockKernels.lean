/-
Copyright (c) 2026. Genuine conditional block heat-bath kernels and parallel blocks.
-/
import Paper09.BlockColoring
import Paper09.Disagreement
import Paper09.Markov
import Paper09.Censoring

open Finset BigOperators Classical Real Matrix
open Paper09.Disagreement

noncomputable section
attribute [local instance] Classical.propDecidable

namespace Paper09.BlockKernels

variable {V : Type*} [Fintype V]

local instance blockSubtypeDecidableEq (B : Finset V) : DecidableEq ↥B := Classical.decEq _

/-- Exact block resampling, keeping every spin outside `B` fixed. -/
def blockHeatBath (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (B : Finset V) (η : Config V) : FinProb (Config V) :=
  Disagreement.condition p hp (Finset.univ \ B) η

theorem agrees_refl (E : Finset V) (η : Config V) : agrees E η η := fun _ _ => rfl

theorem agrees_symm {E : Finset V} {η ξ : Config V} (h : agrees E η ξ) : agrees E ξ η :=
  fun x hx => (h x hx).symm

theorem agrees_trans {E : Finset V} {η ξ ζ : Config V}
    (h1 : agrees E η ξ) (h2 : agrees E ξ ζ) : agrees E η ζ :=
  fun x hx => (h2 x hx).trans (h1 x hx)

theorem agrees_iff_of_agrees {E : Finset V} {η ξ : Config V} (h : agrees E η ξ)
    (ζ : Config V) : agrees E η ζ ↔ agrees E ξ ζ :=
  ⟨fun hz => agrees_trans (agrees_symm h) hz,fun hz => agrees_trans h hz⟩

theorem assignmentMass_eq_of_agrees (p : FinProb (Config V)) {E : Finset V}
    {η ξ : Config V} (h : agrees E η ξ) : assignmentMass p E η = assignmentMass p E ξ := by
  unfold assignmentMass
  simp_rw [agrees_iff_of_agrees h]

theorem condition_eq_of_agrees (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    {E : Finset V} {η ξ : Config V} (h : agrees E η ξ) :
    condition p hp E η = condition p hp E ξ := by
  apply FinProb.ext_weights
  intro ζ
  simp only [condition,assignmentMass_eq_of_agrees p h,agrees_iff_of_agrees h]

/-- Detailed balance of the true full conditional kernel. -/
theorem condition_reversible (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η) (E : Finset V) :
    MarkovKernel.Reversible (fun η => condition p hp E η) p := by
  intro η ξ
  by_cases h : agrees E η ξ
  · have hrev := agrees_symm h
    simp only [condition,if_pos h,if_pos hrev,assignmentMass_eq_of_agrees p h]
    ring
  · have hrev : ¬ agrees E ξ η := fun hh => h (agrees_symm hh)
    simp [condition,h,hrev]

theorem blockHeatBath_reversible (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η) (B : Finset V) :
    MarkovKernel.Reversible (blockHeatBath p hp B) p := condition_reversible p hp _

theorem blockHeatBath_stationary (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η) (B : Finset V) :
    p.bind (blockHeatBath p hp B) = p := by
  apply FinProb.ext_weights
  exact MarkovKernel.stationary_of_reversible _ _ (blockHeatBath_reversible p hp B)

/-- The support condition freezes the exterior exactly. -/
theorem blockHeatBath_support (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (B : Finset V) (η ξ : Config V) (h : (blockHeatBath p hp B η).w ξ ≠ 0) :
    ∀ x, x ∉ B → ξ x = η x := by
  have hs := condition_support p hp (univ\B) η ξ h
  intro x hx
  exact hs x (mem_sdiff.mpr ⟨mem_univ _,hx⟩)

theorem blockHeatBath_self_pos (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (B : Finset V) (η : Config V) : 0 < (blockHeatBath p hp B η).w η := by
  change 0 < (if agrees (univ\B) η η then p.w η else 0) / assignmentMass p (univ\B) η
  rw [if_pos (agrees_refl _ _)]
  exact div_pos (hp η) (assignmentMass_pos p hp _ η)

theorem blockHeatBath_univ (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η) (η : Config V) :
    blockHeatBath p hp univ η = p := by simpa [blockHeatBath] using condition_empty p hp η

/-- A larger block resampling absorbs any preceding update in a subblock. -/
theorem blockHeatBath_absorb_left (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    {A B : Finset V} (hBA : B ⊆ A) (η : Config V) :
    (blockHeatBath p hp B η).bind (blockHeatBath p hp A) = blockHeatBath p hp A η := by
  apply FinProb.ext_weights
  intro ξ
  change (∑ ζ, (blockHeatBath p hp B η).w ζ * (blockHeatBath p hp A ζ).w ξ) = _
  calc
    _ = ∑ ζ, (blockHeatBath p hp B η).w ζ * (blockHeatBath p hp A η).w ξ := by
      apply sum_congr rfl
      intro ζ _
      by_cases hζ : (blockHeatBath p hp B η).w ζ = 0
      · simp [hζ]
      · have heq : blockHeatBath p hp A ζ = blockHeatBath p hp A η := by
          apply condition_eq_of_agrees
          intro x hx
          have hxA := (mem_sdiff.mp hx).2
          have hxB : x ∉ B := fun hb => hxA (hBA hb)
          exact (blockHeatBath_support p hp B η ζ hζ x hxB).symm
        rw [heq]
    _ = _ := by rw [←sum_mul,(blockHeatBath p hp B η).sum_one,one_mul]

/-- Idempotence of exact conditional resampling. -/
theorem blockHeatBath_idempotent (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (B : Finset V) (η : Config V) :
    (blockHeatBath p hp B η).bind (blockHeatBath p hp B) = blockHeatBath p hp B η :=
  blockHeatBath_absorb_left p hp (Subset.refl B) η

/-- Replace the spins of `B` by those of the second configuration. -/
def patch (B : Finset V) (η ξ : Config V) : Config V := fun x => if x ∈ B then ξ x else η x

@[simp] theorem patch_inside (B : Finset V) (η ξ : Config V) {x : V} (hx : x ∈ B) :
    patch B η ξ x = ξ x := by simp [patch,hx]

@[simp] theorem patch_outside (B : Finset V) (η ξ : Config V) {x : V} (hx : x ∉ B) :
    patch B η ξ x = η x := by simp [patch,hx]

theorem patch_agrees (B : Finset V) (η ξ : Config V) : agrees (univ\B) η (patch B η ξ) := by
  intro x hx
  exact patch_outside B η ξ (mem_sdiff.mp hx).2

/-- Swapping the `B` coordinates between a pair is an actual involutive
bijection, used to normalize product conditional densities. -/
def swapPatch (B : Finset V) : Config V × Config V ≃ Config V × Config V where
  toFun p := (patch B p.1 p.2,patch B p.2 p.1)
  invFun p := (patch B p.1 p.2,patch B p.2 p.1)
  left_inv p := by ext x <;> by_cases hx : x ∈ B <;> simp [patch,hx]
  right_inv p := by ext x <;> by_cases hx : x ∈ B <;> simp [patch,hx]

/-- After swapping coordinates, the two separate frozen-exterior constraints
are exactly one fixed reference configuration and one union-block fiber. -/
theorem swap_fiber_iff {B C : Finset V} (hBC : Disjoint B C) (η α β : Config V) :
    (agrees (univ\B) η (patch B α β) ∧ agrees (univ\C) η (patch B β α)) ↔
      α=η ∧ agrees (univ\(B∪C)) η β := by
  constructor
  · rintro ⟨h1,h2⟩
    refine ⟨?_,?_⟩
    · funext x
      by_cases hx : x ∈ B
      · have hxC : x ∉ C := fun hc => Finset.disjoint_left.mp hBC hx hc
        have hh := h2 x (mem_sdiff.mpr ⟨mem_univ _,hxC⟩)
        simpa [patch,hx] using hh
      · have hh := h1 x (mem_sdiff.mpr ⟨mem_univ _,hx⟩)
        simpa [patch,hx] using hh
    · intro x hx
      have hh := h2 x (mem_sdiff.mpr ⟨mem_univ _,fun hc => (mem_sdiff.mp hx).2 (mem_union_right B hc)⟩)
      have hxB : x ∉ B := fun hb => (mem_sdiff.mp hx).2 (mem_union_left C hb)
      simpa [patch,hxB] using hh
  · rintro ⟨hα,hβ⟩
    subst α
    refine ⟨patch_agrees B η β,?_⟩
    intro x hx
    by_cases hxB : x ∈ B
    · simp [patch,hxB]
    · have hxU : x ∉ B∪C := by simp [hxB,(mem_sdiff.mp hx).2]
      have hh := hβ x (mem_sdiff.mpr ⟨mem_univ _,hxU⟩)
      simpa [patch,hxB] using hh

/-- When the union exterior agrees, the complementary patch is precisely
the configuration obtained by changing only `C`. -/
theorem complementary_patch {B C : Finset V} (hBC : Disjoint B C) {η ξ : Config V}
    (hξ : agrees (univ\(B∪C)) η ξ) : patch B ξ η = patch C η ξ := by
  funext x
  by_cases hxB : x ∈ B
  · have hxC : x ∉ C := fun hc => Finset.disjoint_left.mp hBC hxB hc
    simp [patch,hxB,hxC]
  · by_cases hxC : x ∈ C
    · simp [patch,hxB,hxC]
    · have hh := hξ x (mem_sdiff.mpr ⟨mem_univ _,by simp [hxB,hxC]⟩)
      simp [patch,hxB,hxC,hh]

/-- Exact normalizer factorization from a rectangular density identity.
This generic algebra is instantiated below using the actual Ising Hamiltonian. -/
theorem assignmentMass_union_product (p : FinProb (Config V))
    {B C : Finset V} (hBC : Disjoint B C)
    (hrect : ∀ η ξ, agrees (univ\(B∪C)) η ξ →
      p.w η * p.w ξ = p.w (patch B η ξ) * p.w (patch C η ξ)) (η : Config V) :
    assignmentMass p (univ\B) η * assignmentMass p (univ\C) η =
      p.w η * assignmentMass p (univ\(B∪C)) η := by
  let F : Config V × Config V → ℝ := fun z =>
    if agrees (univ\B) η z.1 ∧ agrees (univ\C) η z.2 then p.w z.1 * p.w z.2 else 0
  have hstart : assignmentMass p (univ\B) η * assignmentMass p (univ\C) η = ∑ z, F z := by
    simp only [assignmentMass,F,Fintype.sum_prod_type]
    rw [sum_mul]
    apply sum_congr rfl
    intro α _
    rw [mul_sum]
    apply sum_congr rfl
    intro β _
    by_cases h1 : agrees (univ\B) η α <;> by_cases h2 : agrees (univ\C) η β <;> simp [h1,h2]
  rw [hstart,←(swapPatch B).sum_comp F]
  have hpoint (α β : Config V) : F (swapPatch B (α,β)) =
      if α=η then (if agrees (univ\(B∪C)) η β then p.w η * p.w β else 0) else 0 := by
    change (if agrees (univ\B) η (patch B α β) ∧ agrees (univ\C) η (patch B β α)
      then p.w (patch B α β) * p.w (patch B β α) else 0) = _
    simp only [swap_fiber_iff hBC]
    by_cases hα : α=η
    · subst α
      by_cases hβ : agrees (univ\(B∪C)) η β
      · simp only [hβ,true_and,if_true,complementary_patch hBC hβ]
        exact (hrect η β hβ).symm
      · simp [hβ]
    · simp [hα]
  simp only [Fintype.sum_prod_type,hpoint]
  simp_rw [Finset.sum_ite_irrel,Finset.sum_const_zero]
  simp only [sum_ite_eq',mem_univ,if_true]
  unfold assignmentMass
  rw [mul_sum]
  apply sum_congr rfl
  intro ξ _
  split_ifs <;> simp

/-- A remote, nonadjacent spin does not enter the actual local field. -/
theorem localField_remote_update (Λ : Lattice V) (h : V → ℝ) (β : ℝ)
    (T : Finset V) (φ η : Config V) (x y : V) (hxy : ¬ Λ.adj x y) (v : Spin) :
    localField Λ h β univ T φ (Function.update η y v) x = localField Λ h β univ T φ η x := by
  unfold localField
  congr 2
  congr 1
  apply sum_congr rfl
  intro z _
  by_cases hzy : z=y
  · subst z; simp [hxy]
  · simp [Function.update_of_ne hzy]

/-- Gibbs one-site sampling probabilities are unaffected by a nonneighbor update. -/
theorem plusProbability_remote_update (Λ : Lattice V) (h : V → ℝ) (β : ℝ)
    (T : Finset V) (φ η : Config V) (x y : V) (hxy : ¬ Λ.adj x y) (v : Spin) :
    Censoring.plusProbability (gibbs Λ h β univ T φ) x (Function.update η y v) =
      Censoring.plusProbability (gibbs Λ h β univ T φ) x η := by
  simp only [Censoring.gibbs_plusProbability,localField_remote_update Λ h β T φ η x y hxy v]

/-- Independent local probabilities imply commuting actual one-site Markov
operators; the update values and configurations are explicitly expanded. -/
theorem singleSite_acts_commute (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (x y : V) (hne : x ≠ y)
    (hqx : ∀ η v, Censoring.plusProbability p x (Function.update η y v) = Censoring.plusProbability p x η)
    (hqy : ∀ η v, Censoring.plusProbability p y (Function.update η x v) = Censoring.plusProbability p y η)
    (f : Config V → ℝ) (η : Config V) :
    MarkovKernel.act (Censoring.singleSite p hp x) (MarkovKernel.act (Censoring.singleSite p hp y) f) η =
      MarkovKernel.act (Censoring.singleSite p hp y) (MarkovKernel.act (Censoring.singleSite p hp x) f) η := by
  simp_rw [Censoring.singleSite_act_mixture,hqx,hqy,Function.update_comm hne]
  ring

/-- The actual conditional transition matrices at two nonneighbors commute. -/
theorem gibbs_siteMatrices_commute (Λ : Lattice V) (h : V → ℝ) (β : ℝ)
    (T : Finset V) (φ : Config V) (x y : V) (hne : x ≠ y) (hxy : ¬ Λ.adj x y) :
    Commute (Censoring.siteMatrix (gibbs Λ h β univ T φ) (Censoring.gibbs_positive Λ h β T φ) x)
      (Censoring.siteMatrix (gibbs Λ h β univ T φ) (Censoring.gibbs_positive Λ h β T φ) y) := by
  have hyx : ¬ Λ.adj y x := fun ha => hxy (Λ.symm ha)
  change _ * _ = _ * _
  ext η ξ
  let f : Config V → ℝ := fun ζ => if ζ=ξ then 1 else 0
  have hh := singleSite_acts_commute (gibbs Λ h β univ T φ) (Censoring.gibbs_positive Λ h β T φ)
    x y hne (fun η v => plusProbability_remote_update Λ h β T φ η x y hxy v)
    (fun η v => plusProbability_remote_update Λ h β T φ η y x hyx v) f η
  change (Censoring.siteMatrix _ _ x *ᵥ (Censoring.siteMatrix _ _ y *ᵥ f)) η =
    (Censoring.siteMatrix _ _ y *ᵥ (Censoring.siteMatrix _ _ x *ᵥ f)) η at hh
  rw [Matrix.mulVec_mulVec,Matrix.mulVec_mulVec] at hh
  simpa [Matrix.mulVec,dotProduct,f] using hh

/-- Two disjoint, nonadjacent blocks have commuting rate-one generators. -/
theorem gibbs_blockGenerators_commute (Λ : Lattice V) (h : V → ℝ) (β : ℝ)
    (T : Finset V) (φ : Config V) (B C : Finset V) (hBC : Disjoint B C)
    (hno : ∀ x ∈ B, ∀ y ∈ C, ¬ Λ.adj x y) :
    Commute (Censoring.siteGenerator (gibbs Λ h β univ T φ) (Censoring.gibbs_positive Λ h β T φ) B)
      (Censoring.siteGenerator (gibbs Λ h β univ T φ) (Censoring.gibbs_positive Λ h β T φ) C) := by
  unfold Censoring.siteGenerator
  apply Commute.sum_left
  intro x hx
  apply Commute.sum_right
  intro y hy
  have hne : x ≠ y := fun heq => Finset.disjoint_left.mp hBC hx (heq ▸ hy)
  have hc := gibbs_siteMatrices_commute Λ h β T φ x y hne (hno x hx y hy)
  exact (hc.sub_right (Commute.one_right _)).sub_left (Commute.one_left _)

/-- Retaining the union of two disjoint blocks adds their actual generators. -/
theorem siteGenerator_union (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (B C : Finset V) (hBC : Disjoint B C) :
    Censoring.siteGenerator p hp (B∪C) = Censoring.siteGenerator p hp B + Censoring.siteGenerator p hp C :=
  Finset.sum_union hBC

/-- Exact physical parallelism: running the union's rate-one clocks for time
`t` equals composing the two frozen-exterior block semigroups for the same time. -/
theorem gibbs_siteSemigroup_union (Λ : Lattice V) (h : V → ℝ) (β : ℝ)
    (T : Finset V) (φ : Config V) (B C : Finset V) (hBC : Disjoint B C)
    (hno : ∀ x ∈ B, ∀ y ∈ C, ¬ Λ.adj x y) (t : ℝ) :
    Censoring.siteSemigroup (gibbs Λ h β univ T φ) (Censoring.gibbs_positive Λ h β T φ) (B∪C) t =
      Censoring.siteSemigroup (gibbs Λ h β univ T φ) (Censoring.gibbs_positive Λ h β T φ) B t *
      Censoring.siteSemigroup (gibbs Λ h β univ T φ) (Censoring.gibbs_positive Λ h β T φ) C t := by
  unfold Censoring.siteSemigroup
  rw [siteGenerator_union _ _ B C hBC,smul_add]
  apply Matrix.exp_add_of_commute
  have hc := gibbs_blockGenerators_commute Λ h β T φ B C hBC hno
  change (t • _) * (t • _) = (t • _) * (t • _)
  simp only [Matrix.mul_smul,Matrix.smul_mul,smul_smul]
  rw [hc.eq]

/-- Sequential composition of the actual frozen-exterior block semigroups.
Every factor is run for the same physical time, not a fraction of that time. -/
def parallelMatrix {ι : Type*} (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (B : ι → Finset V) (l : List ι) (t : ℝ) : Matrix (Config V) (Config V) ℝ :=
  (l.map (fun i => Censoring.siteSemigroup p hp (B i) t)).prod

/-- Finite parallel decomposition for any actual pairwise-disjoint,
nonadjacent lattice blocks. -/
theorem gibbs_siteSemigroup_biUnion {ι : Type*} [DecidableEq ι]
    (Λ : Lattice V) (h : V → ℝ) (β : ℝ) (T : Finset V) (φ : Config V)
    (B : ι → Finset V) (l : List ι)
    (hl : l.Pairwise (fun i j => Disjoint (B i) (B j) ∧
      ∀ x ∈ B i, ∀ y ∈ B j, ¬ Λ.adj x y)) (t : ℝ) :
    Censoring.siteSemigroup (gibbs Λ h β univ T φ) (Censoring.gibbs_positive Λ h β T φ)
      (l.toFinset.biUnion B) t =
      parallelMatrix (gibbs Λ h β univ T φ) (Censoring.gibbs_positive Λ h β T φ) B l t := by
  induction l with
  | nil => simp [parallelMatrix,Censoring.siteSemigroup,Censoring.siteGenerator]
  | cons i l ih =>
    obtain ⟨hhead,htail⟩ := List.pairwise_cons.mp hl
    have hdisj : Disjoint (B i) (l.toFinset.biUnion B) := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      obtain ⟨j,hj,hxj⟩ := Finset.mem_biUnion.mp hy
      exact Finset.disjoint_left.mp (hhead j (List.mem_toFinset.mp hj)).1 hx hxj
    have hno : ∀ x ∈ B i, ∀ y ∈ l.toFinset.biUnion B, ¬ Λ.adj x y := by
      intro x hx y hy
      obtain ⟨j,hj,hyj⟩ := Finset.mem_biUnion.mp hy
      exact (hhead j (List.mem_toFinset.mp hj)).2 x hx y hyj
    simp only [List.toFinset_cons,Finset.biUnion_insert]
    rw [gibbs_siteSemigroup_union Λ h β T φ _ _ hdisj hno t,ih htail]
    rfl

/-- At the level of actual stochastic kernels, union-block CT evolution is
composition of the two physical block evolutions. -/
theorem gibbs_siteTransition_union (Λ : Lattice V) (h : V → ℝ) (β : ℝ)
    (T : Finset V) (φ : Config V) (B C : Finset V) (hBC : Disjoint B C)
    (hno : ∀ x ∈ B, ∀ y ∈ C, ¬ Λ.adj x y) (t : ℝ) (η : Config V) :
    (Censoring.siteTransition (gibbs Λ h β univ T φ) (Censoring.gibbs_positive Λ h β T φ) B t η).bind
      (Censoring.siteTransition (gibbs Λ h β univ T φ) (Censoring.gibbs_positive Λ h β T φ) C t) =
      Censoring.siteTransition (gibbs Λ h β univ T φ) (Censoring.gibbs_positive Λ h β T φ) (B∪C) t η := by
  apply FinProb.ext_weights
  intro ξ
  change (∑ ζ, Censoring.siteSemigroup _ _ B (max t 0) η ζ *
    Censoring.siteSemigroup _ _ C (max t 0) ζ ξ) = Censoring.siteSemigroup _ _ (B∪C) (max t 0) η ξ
  rw [gibbs_siteSemigroup_union Λ h β T φ B C hBC hno]
  rfl

/-- Instantiation on the real covering's finite-volume site subtype. The
membership and adjacency equations merely identify the caller's subtype
notation with the constructed blocks and actual nearest-neighbor graph. -/
theorem same_color_siteSemigroup_parallel {d : ℕ} {good : LatticeGeometry.Point d → Prop}
    {n s : ℕ} {α : Type*}
    (Λ : Lattice ↥(BlockCovering.volume (d:=d) n))
    (hΛ : ∀ x y, Λ.adj x y ↔ LatticeGeometry.Adj x.val y.val)
    (h : ↥(BlockCovering.volume (d:=d) n) → ℝ) (β : ℝ)
    (T : Finset ↥(BlockCovering.volume (d:=d) n))
    (φ : Config ↥(BlockCovering.volume (d:=d) n))
    (B : BlockCovering.BlockIndex good n s → Finset ↥(BlockCovering.volume (d:=d) n))
    (hB : ∀ i x, x ∈ B i ↔ x.val ∈ BlockCovering.block i)
    (c : (BlockColoring.conflictGraph good n s).Coloring α) (a : α) (t : ℝ) :
    Censoring.siteSemigroup (gibbs Λ h β univ T φ) (Censoring.gibbs_positive Λ h β T φ)
      ((BlockColoring.classIndices c a).biUnion B) t =
      parallelMatrix (gibbs Λ h β univ T φ) (Censoring.gibbs_positive Λ h β T φ)
        B (BlockColoring.classIndices c a).toList t := by
  classical
  have hpair : (BlockColoring.classIndices c a).toList.Pairwise
      (fun i j => Disjoint (B i) (B j) ∧ ∀ x ∈ B i, ∀ y ∈ B j, ¬ Λ.adj x y) := by
    apply (BlockColoring.classIndices c a).nodup_toList.pairwise_of_forall_ne
    intro i hi j hj hne
    have hci := BlockColoring.mem_classIndices.mp (Finset.mem_toList.mp hi)
    have hcj := BlockColoring.mem_classIndices.mp (Finset.mem_toList.mp hj)
    have hcolor := hci.trans hcj.symm
    refine ⟨?_,?_⟩
    · apply Finset.disjoint_left.mpr
      intro x hxi hxj
      exact Finset.disjoint_left.mp (BlockColoring.same_color_blocks_disjoint c hne hcolor)
        ((hB i x).mp hxi) ((hB j x).mp hxj)
    · intro x hxi y hyj hxy
      exact BlockColoring.same_color_no_edge c hne hcolor ((hB i x).mp hxi) ((hB j y).mp hyj)
        ((hΛ x y).mp hxy)
  simpa using gibbs_siteSemigroup_biUnion Λ h β T φ B (BlockColoring.classIndices c a).toList hpair t

/-- Restrict a full configuration to the actual finite block subtype. -/
def restrictConfig (B : Finset V) (η : Config V) : Config ↥B := fun x => η x.val

/-- Embed local spins while retaining the prescribed exterior configuration. -/
def embedConfig (B : Finset V) (η : Config V) (σ : Config ↥B) : Config V :=
  fun x => if hx : x ∈ B then σ ⟨x,hx⟩ else η x

@[simp] theorem restrict_embed (B : Finset V) (η : Config V) (σ : Config ↥B) :
    restrictConfig B (embedConfig B η σ) = σ := by
  funext x
  simp [restrictConfig,embedConfig,x.property]

@[simp] theorem embed_restrict_self (B : Finset V) (η : Config V) :
    embedConfig B η (restrictConfig B η) = η := by
  funext x
  by_cases hx : x ∈ B <;> simp [embedConfig,restrictConfig,hx]

theorem embedConfig_injective (B : Finset V) (η : Config V) :
    Function.Injective (embedConfig B η) := by
  intro σ τ heq
  have hh := congrArg (restrictConfig B) heq
  simpa using hh

theorem embed_agrees (B : Finset V) (η : Config V) (σ : Config ↥B) :
    agrees (univ\B) η (embedConfig B η σ) := by
  intro x hx
  simp [embedConfig,(mem_sdiff.mp hx).2]

theorem embed_restrict_of_agrees (B : Finset V) (η ξ : Config V)
    (hξ : agrees (univ\B) η ξ) : embedConfig B η (restrictConfig B ξ) = ξ := by
  funext x
  by_cases hx : x ∈ B
  · simp [embedConfig,restrictConfig,hx]
  · simp [embedConfig,hx,hξ x (mem_sdiff.mpr ⟨mem_univ _,hx⟩)]

/-- The genuine conditional Gibbs law on the smaller configuration space. -/
def localConditional (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (B : Finset V) (η : Config V) : FinProb (Config ↥B) :=
  (blockHeatBath p hp B η).map (restrictConfig B)

/-- Its explicit mass is the original Gibbs mass divided by the actual
outside-assignment probability, with no artificial free coordinates. -/
theorem localConditional_w (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (B : Finset V) (η : Config V) (σ : Config ↥B) :
    (localConditional p hp B η).w σ = p.w (embedConfig B η σ) / assignmentMass p (univ\B) η := by
  dsimp only [localConditional,FinProb.map]
  rw [sum_eq_single (embedConfig B η σ)]
  · simp [blockHeatBath,condition,embed_agrees]
  · intro ξ _ hξ
    by_cases hrestr : restrictConfig B ξ=σ
    · have hzero : (blockHeatBath p hp B η).w ξ=0 := by
        by_contra hn
        have hsupport := condition_support p hp (univ\B) η ξ hn
        have heq := embed_restrict_of_agrees B η ξ hsupport
        rw [hrestr] at heq
        exact hξ heq.symm
      simp [hzero]
    · simp [hrestr]
  · simp

theorem localConditional_positive (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (B : Finset V) (η : Config V) (σ : Config ↥B) : 0 < (localConditional p hp B η).w σ := by
  rw [localConditional_w]
  exact div_pos (hp _) (assignmentMass_pos p hp _ _)

/-- Embedding the actual local conditional law recovers full block resampling. -/
theorem localConditional_embed (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (B : Finset V) (η : Config V) :
    (localConditional p hp B η).map (embedConfig B η) = blockHeatBath p hp B η := by
  apply FinProb.ext_weights
  intro ξ
  dsimp only [FinProb.map]
  by_cases hξ : agrees (univ\B) η ξ
  · have hembed := embed_restrict_of_agrees B η ξ hξ
    have heq (σ : Config ↥B) : embedConfig B η σ=ξ ↔ σ=restrictConfig B ξ := by
      constructor
      · intro hh
        have hh' := congrArg (restrictConfig B) hh
        simpa using hh'
      · intro hh
        rw [hh]
        exact hembed
    simp_rw [heq]
    simp only [sum_ite_eq',mem_univ,if_true,localConditional_w,hembed]
    simp [blockHeatBath,condition,hξ]
  · have hne (σ : Config ↥B) : embedConfig B η σ ≠ ξ := by
      intro heq
      exact hξ (heq ▸ embed_agrees B η σ)
    simp [hne,blockHeatBath,condition,hξ]

theorem map_w_expect {α β : Type*} [Fintype α] [Fintype β]
    (p : FinProb α) (f : α → β) (b : β) :
    (p.map f).w b = p.expect (fun a => if f a=b then 1 else 0) := by
  simp [FinProb.map,FinProb.expect,mul_ite]

/-- Finite pushforward contracts total variation, including injective frozen-
exterior embeddings. -/
theorem tvDist_map_le {α β : Type*} [Fintype α] [Fintype β]
    (p q : FinProb α) (f : α → β) : tvDist (p.map f) (q.map f) ≤ tvDist p q := by
  have he (b : β) : (p.map f).w b-(q.map f).w b =
      ∑ a, if f a=b then p.w a-q.w a else 0 := by
    simp only [FinProb.map,←sum_sub_distrib]
    apply sum_congr rfl
    intro a _
    split_ifs <;> ring
  unfold tvDist
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    ∑ b, |(p.map f).w b-(q.map f).w b| ≤ ∑ b, ∑ a, |if f a=b then p.w a-q.w a else 0| := by
      apply sum_le_sum
      intro b _
      rw [he]
      exact abs_sum_le_sum_abs _ _
    _ = ∑ a, |p.w a-q.w a| := by
      rw [sum_comm]
      apply sum_congr rfl
      intro a _
      simp only [apply_ite abs,abs_zero,sum_ite_eq,mem_univ,if_true]

/-- Local spin replacement commutes exactly with the frozen-exterior embedding. -/
theorem embed_update (B : Finset V) (η : Config V) (σ : Config ↥B) (x : ↥B) (v : Spin) :
    embedConfig B η (Function.update σ x v) = Function.update (embedConfig B η σ) x.val v := by
  funext y
  by_cases hyx : y=x.val
  · subst y
    simp [embedConfig,x.property]
  · by_cases hyB : y ∈ B
    · have hne : (⟨y,hyB⟩ : ↥B) ≠ x := fun hh => hyx (congrArg Subtype.val hh)
      simp [embedConfig,hyB,Function.update_of_ne hne,Function.update_of_ne hyx]
    · simp [embedConfig,hyB,Function.update_of_ne hyx]

/-- The actual one-site conditional chain on the smaller configuration space
is the ambient one-site chain with exterior spins fixed. -/
theorem singleSite_local_act (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (B : Finset V) (η : Config V) (σ : Config ↥B) (x : ↥B) (f : Config V → ℝ) :
    MarkovKernel.act
      (Censoring.singleSite (localConditional p hp B η) (localConditional_positive p hp B η) x)
      (fun τ => f (embedConfig B η τ)) σ =
      MarkovKernel.act (Censoring.singleSite p hp x.val) f (embedConfig B η σ) := by
  rw [Censoring.singleSite_act_binary,Censoring.singleSite_act_binary]
  simp_rw [localConditional_w,embed_update]
  have hm : assignmentMass p (univ\B) η ≠ 0 := (assignmentMass_pos p hp _ _).ne'
  have hab : p.w (Function.update (embedConfig B η σ) x.val 0) +
      p.w (Function.update (embedConfig B η σ) x.val 1) ≠ 0 := ne_of_gt (add_pos (hp _) (hp _))
  field_simp [hm,hab]
  <;> ring

/-- Intertwining of the true rate-one block generator with the full smaller
heat-bath generator, including the exact original time normalization. -/
theorem siteGenerator_local_act (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (B : Finset V) (η : Config V) (σ : Config ↥B) (f : Config V → ℝ) :
    (Censoring.siteGenerator p hp B *ᵥ f) (embedConfig B η σ) =
      (Censoring.siteGenerator (localConditional p hp B η) (localConditional_positive p hp B η) univ *ᵥ
        (fun τ => f (embedConfig B η τ))) σ := by
  rw [Censoring.siteGenerator_apply,Censoring.siteGenerator_apply]
  symm
  calc
    (∑ x : ↥B, (MarkovKernel.act
        (Censoring.singleSite (localConditional p hp B η) (localConditional_positive p hp B η) x)
        (fun τ => f (embedConfig B η τ)) σ - f (embedConfig B η σ))) =
        ∑ x : ↥B, (MarkovKernel.act (Censoring.singleSite p hp x.val) f (embedConfig B η σ) -
          f (embedConfig B η σ)) := by simp_rw [singleSite_local_act]
    _ = ∑ x ∈ B, (MarkovKernel.act (Censoring.singleSite p hp x) f (embedConfig B η σ) -
          f (embedConfig B η σ)) := Finset.sum_coe_sort B
        (fun x : V => MarkovKernel.act (Censoring.singleSite p hp x) f (embedConfig B η σ) -
          f (embedConfig B η σ))

private theorem exp_action_hasSum {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℝ) (f : α → ℝ) (a : α) :
    HasSum (fun n : ℕ => (n.factorial : ℝ)⁻¹ * ((M^n)*ᵥf) a)
      (((NormedSpace.exp ℝ M)*ᵥf) a) := by
  have hh := hasSum_sum (fun b (_ : b ∈ (univ : Finset α)) =>
    (matrix_exp_hasSum M a b).mul_right (f b))
  convert hh using 1
  funext n
  simp only [Matrix.mulVec,dotProduct,mul_sum]
  apply sum_congr rfl
  intro b _
  ring

/-- Exponentiation preserves an actual generator intertwining, proved from
the absolutely convergent matrix exponential series. -/
theorem matrix_exp_action_intertwine {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (A : Matrix α α ℝ) (D : Matrix β β ℝ) (e : β → α)
    (hAD : ∀ f a, (A*ᵥf) (e a) = (D*ᵥ(fun b => f (e b))) a) (f : α → ℝ) (a : β) :
    ((NormedSpace.exp ℝ A)*ᵥf) (e a) = ((NormedSpace.exp ℝ D)*ᵥ(fun b => f (e b))) a := by
  have hp : ∀ n : ℕ, ∀ a, ((A^n)*ᵥf) (e a) = ((D^n)*ᵥ(fun b => f (e b))) a := by
    intro n
    induction n with
    | zero => intro a; simp
    | succ n ih =>
      intro a
      rw [pow_succ',←Matrix.mulVec_mulVec,hAD]
      have heq : (fun b => ((A^n)*ᵥf) (e b)) = (D^n)*ᵥ(fun b => f (e b)) := funext ih
      rw [heq,Matrix.mulVec_mulVec,←pow_succ']
  have h1 := exp_action_hasSum A f (e a)
  have h2 := exp_action_hasSum D (fun b => f (e b)) a
  exact h1.unique (h2.congr_fun (fun n => by rw [hp]))

/-- Exact embedding of the full local CT heat-bath law into the ambient frozen-
exterior block dynamics. This transfers local A.1/A.2 mixing bounds without
changing the clock rate or paying for the ambient volume. -/
theorem siteTransition_local_embed (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (B : Finset V) (η : Config V) (σ : Config ↥B) (t : ℝ) :
    Censoring.siteTransition p hp B t (embedConfig B η σ) =
      (heatBathTransition (localConditional p hp B η) t σ).map (embedConfig B η) := by
  apply FinProb.ext_weights
  intro ξ
  let f : Config V → ℝ := fun ζ => if ζ=ξ then 1 else 0
  have hinter : ∀ g a,
      ((max t 0 • Censoring.siteGenerator p hp B)*ᵥg) (embedConfig B η a) =
      ((max t 0 • Censoring.siteGenerator (localConditional p hp B η)
        (localConditional_positive p hp B η) univ)*ᵥ(fun b => g (embedConfig B η b))) a := by
    intro g a
    simp only [Matrix.smul_mulVec,Pi.smul_apply,smul_eq_mul,siteGenerator_local_act]
  have hh := matrix_exp_action_intertwine _ _ (embedConfig B η) hinter f σ
  rw [Censoring.siteGenerator_univ] at hh
  change (NormedSpace.exp ℝ (max t 0 • Censoring.siteGenerator p hp B) *ᵥf) (embedConfig B η σ) =
    (NormedSpace.exp ℝ (max t 0 • heatBathMatrix (localConditional p hp B η)) *ᵥ
      (fun b => f (embedConfig B η b))) σ at hh
  rw [map_w_expect]
  dsimp only [Censoring.siteTransition,heatBathTransition,FinProb.expect]
  simpa only [Matrix.mulVec,dotProduct,f,mul_ite,mul_one,mul_zero,sum_ite_eq',mem_univ,if_true,
    Censoring.siteSemigroup,heatBathSemigroup] using hh

/-- Uniform local total-variation approximation transfers directly to the
physical ambient block evolution and its actual conditional equilibrium law. -/
theorem block_ct_mixing_error (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (B : Finset V) (η : Config V) (t δ : ℝ)
    (hlocal : ∀ σ : Config ↥B,
      tvDist (heatBathTransition (localConditional p hp B η) t σ) (localConditional p hp B η) ≤ δ) :
    tvDist (Censoring.siteTransition p hp B t η) (blockHeatBath p hp B η) ≤ δ := by
  have hstep := siteTransition_local_embed p hp B η (restrictConfig B η) t
  rw [embed_restrict_self] at hstep
  rw [hstep,←localConditional_embed p hp B η]
  exact (tvDist_map_le _ _ (embedConfig B η)).trans (hlocal _)

/-- Exact finite pushforward composition. -/
theorem map_map {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (p : FinProb α) (f : α → β) (g : β → γ) :
    (p.map f).map g = p.map (fun a => g (f a)) := by
  apply FinProb.ext_weights
  intro c
  rw [map_w_expect,FinProb.expect_map,map_w_expect]

/-- The physical block CT kernel keeps the entire exterior frozen. -/
theorem siteTransition_frozen (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (B : Finset V) (t : ℝ) (η ξ : Config V)
    (hξ : (Censoring.siteTransition p hp B t η).w ξ ≠ 0) :
    ∀ x, x ∉ B → ξ x = η x := by
  have heq := siteTransition_local_embed p hp B η (restrictConfig B η) t
  rw [embed_restrict_self] at heq
  intro x hx
  by_contra hspin
  have hne (σ : Config ↥B) : embedConfig B η σ ≠ ξ := by
    intro hh
    have hh' := congrFun hh x
    exact hspin (by simpa [embedConfig,hx] using hh'.symm)
  rw [heq] at hξ
  exact hξ (by simp [FinProb.map,hne])

theorem localConditional_w_blockHeatBath (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (B : Finset V) (η : Config V) (σ : Config ↥B) :
    (localConditional p hp B η).w σ = (blockHeatBath p hp B η).w (embedConfig B η σ) := by
  rw [localConditional_w]
  simp [blockHeatBath,condition,embed_agrees]

/-- The actual finite-volume Gibbs specification depends only on the block's
relative external vertex boundary, after restriction to the local spins. -/
theorem gibbs_localConditional_eq_of_boundary_agrees (Λ : Lattice V) (h : V → ℝ) (β : ℝ)
    (T B : Finset V) (φ η ξ : Config V)
    (hboundary : ∀ x ∈ Λ.boundary B, η x = ξ x) :
    localConditional (gibbs Λ h β univ T φ) (Censoring.gibbs_positive Λ h β T φ) B η =
      localConditional (gibbs Λ h β univ T φ) (Censoring.gibbs_positive Λ h β T φ) B ξ := by
  apply FinProb.ext_weights
  intro σ
  rw [localConditional_w_blockHeatBath,localConditional_w_blockHeatBath]
  have hE : ∀ u ∈ univ\(univ\B), ∀ v ∈ univ\B, Λ.adj u v → η v = ξ v := by
    intro u hu v hv hadj
    have huB : u ∈ B := by simpa using hu
    have hvB := (mem_sdiff.mp hv).2
    exact hboundary v ((Λ.mem_boundary).mpr ⟨hvB,u,huB,hadj⟩)
  have hh := gibbs_spatial_markov Λ h β univ T (univ\B) φ φ η ξ hE
    (fun _ _ _ _ _ => rfl) (embedConfig B η σ)
  have htransport : assignmentEquiv (univ\B) η ξ (embedConfig B η σ) = embedConfig B ξ σ := by
    funext x
    by_cases hx : x ∈ B <;> simp [assignmentEquiv,embedConfig,hx]
  simpa only [blockHeatBath,htransport] using hh

/-- The ambient CT law is the same local chain when the two initial states
agree on the block and its boundary; only their frozen exterior is changed.
This is the locality needed to couple all unaffected color blocks identically. -/
theorem gibbs_siteTransition_boundary_transport (Λ : Lattice V) (h : V → ℝ) (β : ℝ)
    (T B : Finset V) (φ η ξ : Config V)
    (hinside : agrees B η ξ) (hboundary : ∀ x ∈ Λ.boundary B, η x = ξ x) (t : ℝ) :
    (Censoring.siteTransition (gibbs Λ h β univ T φ) (Censoring.gibbs_positive Λ h β T φ) B t η).map
      (fun ζ => embedConfig B ξ (restrictConfig B ζ)) =
    Censoring.siteTransition (gibbs Λ h β univ T φ) (Censoring.gibbs_positive Λ h β T φ) B t ξ := by
  have hη := siteTransition_local_embed (gibbs Λ h β univ T φ) (Censoring.gibbs_positive Λ h β T φ)
    B η (restrictConfig B η) t
  have hξ := siteTransition_local_embed (gibbs Λ h β univ T φ) (Censoring.gibbs_positive Λ h β T φ)
    B ξ (restrictConfig B ξ) t
  rw [embed_restrict_self] at hη hξ
  rw [hη,hξ,map_map]
  have hlaw := gibbs_localConditional_eq_of_boundary_agrees Λ h β T B φ η ξ hboundary
  have hrestrict : restrictConfig B η = restrictConfig B ξ := by
    funext x
    exact (hinside x.val x.property).symm
  rw [hlaw,hrestrict]
  congr 1
  funext σ
  rw [restrict_embed]

/-- Patch notation for the CT locality interface: agreeing on a block closure
allows identical local evolution and a deterministic change of frozen exterior. -/
theorem gibbs_siteTransition_closure_transport (Λ : Lattice V) (h : V → ℝ) (β : ℝ)
    (T B : Finset V) (φ η ξ : Config V)
    (hclosure : ∀ x ∈ B ∪ Λ.boundary B, η x = ξ x) (t : ℝ) :
    (Censoring.siteTransition (gibbs Λ h β univ T φ) (Censoring.gibbs_positive Λ h β T φ) B t η).map
      (patch B ξ) =
    Censoring.siteTransition (gibbs Λ h β univ T φ) (Censoring.gibbs_positive Λ h β T φ) B t ξ := by
  have hmap : (fun ζ => embedConfig B ξ (restrictConfig B ζ)) = patch B ξ := by
    funext ζ x
    by_cases hx : x ∈ B <;> simp [embedConfig,restrictConfig,patch,hx]
  rw [←hmap]
  exact gibbs_siteTransition_boundary_transport Λ h β T B φ η ξ
    (fun x hx => (hclosure x (mem_union_left _ hx)).symm)
    (fun x hx => hclosure x (mem_union_right _ hx)) t

end Paper09.BlockKernels
