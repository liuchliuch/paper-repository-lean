import Paper18.Fusion.Constructions
import Paper18.Results.Integrality
import Paper18.Fusion.Pivotal
import Paper18.Fusion.Braided
import Paper18.Fusion.Grading
import Paper18.Fusion.Sphericalization
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Theorem 1.1 — Galois–modular extensions for Tannakian centers

*Let `ℬ` be a premodular fusion category with specified spherical structure and
`Z₂(ℬ) ≅ Rep(G)` as braided fusion categories.  There exist a modular fusion
category `ℳ` and a fully faithful braided spherical tensor functor `ℬ ↪ ℳ`
such that `ℬ'_ℳ` is integral.*

This module proves some conditional algebraic reductions of §3
about the combinatorial fusion interface `Paper18.Fusion.*`:

* `sign_character_values` — (3.4): `χ_X ∈ {1,-1}` from `χ_{X*} = χ_X^{-1}`
  (tensor automorphism of `id`) together with `χ_X = χ_{X*}` (both spherical).
* `chi_epsilon_eq_neg_one` — (3.5): `χ_ε = -1` on the order-two lift
  `ε = (1,-id)`, whose inherited dimension is `-1` and positive dimension `+1`.
* `case1_integrality` — Case 1 (`χ|_ℰ = 1`): FP-dimension preservation of the
  `ℤ/2`-grading by monodromy with `e`, together with Lemma 3.1
  equivariantization, makes `𝒦` integral.
* `case2_centralizer_dim` — Case 2, equation (3.6): the centralizer-dimension
  identity for index two yields `(𝒦₊)'_𝒦 = ℰ` and `Z₂(𝒦₊) = ℰ₊`.
* `case2_D_integrality` — Case 2, equations (3.10)–(3.11): `𝒟 = ℰ ∨ ℐ^rev` with
  `FPdim(𝒟) = 2 FPdim(ℐ)`, and a dominant tensor functor from the integral
  source `ℰ ⊠ ℐ^rev` makes `𝒟` integral.

External black boxes ([JF, Prop. 2.3], ENO pseudounitarity, Proposition 2.2,
Lemma 3.1 equivariantization, diagonal condensation) appear as **explicit
data packages** below. Their existence and connection to actual categories
are not proved. `theorem1_1_reduction` is not the paper's main theorem.
-/

noncomputable section

open Classical

universe u

open scoped BigOperators

namespace Paper18

/-! ## Elementary based-ring identities -/

/-- Frobenius reciprocity shadow: `N x x* 1 = 1`.  Derived from `N_dual` and
`N_one_right` in `FusionBasis`. -/
lemma N_self_dual_one {ι : Type u} [Fintype ι] (B : FusionBasis ι) (x : ι) :
    B.N x (B.dual x) B.one = 1 := by
  rw [B.N_dual, B.N_one_right]
  simp

/-- Total FP dimension of a set of simples: `∑_{x ∈ s} fpdim x ^ 2`. -/
def FusionBasis.subFPdim {ι : Type u} [Fintype ι] (B : FusionBasis ι)
    (s : Set ι) : ℝ :=
  ∑ x ∈ s.toFinset, B.fpdim x ^ 2

/-- Two fusion subcategories with one contained in the other and equal total FP
dimension coincide (FP dimensions of simples are strictly positive). -/
theorem eq_of_subset_subFPdim {ι : Type u} [Fintype ι] {B : FusionBasis ι}
    {s t : Set ι} (hsub : s ⊆ t) (heq : B.subFPdim s = B.subFPdim t) :
    s = t := by
  classical
  have hst : s.toFinset ⊆ t.toFinset := by
    intro x hx
    have hx' : x ∈ s := by simpa using hx
    have : x ∈ t := hsub hx'
    simpa using this
  have hsplit : ∑ x ∈ t.toFinset \ s.toFinset, B.fpdim x ^ 2
        + ∑ x ∈ s.toFinset, B.fpdim x ^ 2
      = ∑ x ∈ t.toFinset, B.fpdim x ^ 2 :=
    Finset.sum_sdiff hst
  have hdiff : ∑ x ∈ t.toFinset \ s.toFinset, B.fpdim x ^ 2 = 0 := by
    have hre : (0 : ℝ)
        = ∑ x ∈ t.toFinset, B.fpdim x ^ 2 - ∑ x ∈ s.toFinset, B.fpdim x ^ 2 := by
      have h1 : B.subFPdim s = ∑ x ∈ s.toFinset, B.fpdim x ^ 2 := rfl
      have h2 : B.subFPdim t = ∑ x ∈ t.toFinset, B.fpdim x ^ 2 := rfl
      rw [← h1, ← h2, heq]
      ring
    linarith [hsplit]
  have hzero : ∀ x ∈ t.toFinset \ s.toFinset, B.fpdim x ^ 2 = 0 := by
    intro x hx
    by_contra hne
    have hpos : 0 < B.fpdim x ^ 2 := sq_pos_of_ne_zero (ne_of_gt (B.fpdim_pos x))
    have hsum := (Finset.sum_eq_zero_iff_of_nonneg
      (fun (i : ι) (_ : i ∈ t.toFinset \ s.toFinset) => sq_nonneg (B.fpdim i))).mp hdiff
    exact hne (hsum x hx)
  have hss : t.toFinset = s.toFinset := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      by_contra hns
      have hmem : x ∈ t.toFinset \ s.toFinset := by
        refine Finset.mem_sdiff.mpr ⟨hx, hns⟩
      have := hzero x hmem
      have hpos : 0 < B.fpdim x := B.fpdim_pos x
      have h2 : B.fpdim x = 0 := pow_eq_zero this
      exact absurd h2 (ne_of_gt hpos)
    · exact Finset.card_le_card hst
  have hss' : s.toFinset = t.toFinset := hss.symm
  exact Set.toFinset_inj.mp hss'

/-! ## Sign characters (paper §3, equation (3.4)) -/

/-- **`sign_character_values`.**  Paper (3.4): a nonzero scalar function on
simples satisfying `χ_{X*} = χ_X^{-1}` (tensor automorphism of the identity) and
`χ_X = χ_{X*}` (ratio of two spherical structures, since `FPdim(X)=FPdim(X*)`)
takes values in `{1,-1}`. -/
theorem sign_character_values {ι : Type u} [Fintype ι] {B : FusionBasis ι}
    (χ : ι → ℂ) (hne : ∀ x, χ x ≠ 0)
    (hdual_inv : ∀ x, χ (B.dual x) = (χ x)⁻¹)
    (hdual_eq : ∀ x, χ (B.dual x) = χ x) :
    ∀ x, χ x = 1 ∨ χ x = -1 := by
  intro x
  have hinv : χ x = (χ x)⁻¹ := by
    rw [← hdual_inv x, hdual_eq x]
  have h2 : χ x ^ 2 = 1 := by
    have hmul : χ x * χ x = 1 := by
      nth_rw 2 [hinv]
      exact mul_inv_cancel₀ (hne x)
    rwa [pow_two]
  have hfac : (χ x - 1) * (χ x + 1) = 0 := by
    have hring : (χ x - 1) * (χ x + 1) = χ x ^ 2 - 1 := by ring
    rw [hring, h2]
    ring
  rcases mul_eq_zero.mp hfac with h | h
  · left; exact sub_eq_zero.mp h
  · right; exact add_eq_zero_iff_eq_neg.mp h

/-- Helper: `χ_{X*} = χ_X^{-1}` from multiplicativity and `N x x* 1 = 1`. -/
theorem chi_dual_inv {ι : Type u} [Fintype ι] {B : FusionBasis ι}
    (χ : ι → ℂ) (hone : χ B.one = 1) (hχ_ne : ∀ x, χ x ≠ 0)
    (hχ_mul : ∀ x y z, 0 < B.N x y z → χ z = χ x * χ y) :
    ∀ x, χ (B.dual x) = (χ x)⁻¹ := by
  intro x
  have h1 : χ B.one = χ x * χ (B.dual x) :=
    hχ_mul x (B.dual x) B.one (by rw [N_self_dual_one]; exact one_pos)
  have hcalc : χ x * χ (B.dual x) = 1 := by
    rw [← h1, hone]
  have hne : χ x ≠ 0 := hχ_ne x
  calc χ (B.dual x) = 1 * χ (B.dual x) := (one_mul _).symm
    _ = ((χ x)⁻¹ * χ x) * χ (B.dual x) := by rw [inv_mul_cancel₀ hne]
    _ = (χ x)⁻¹ * (χ x * χ (B.dual x)) := by ring
    _ = (χ x)⁻¹ * 1 := by rw [hcalc]
    _ = (χ x)⁻¹ := mul_one _

/-- The ratio `χ_X = j_X / j⁺_X` of a spherical structure `j` to a spherical
structure `j⁺`, when it is multiplicative along tensor (i.e. `j = j⁺ χ` as a
tensor automorphism of the identity), is a sign character. -/
def SignCharacter.ofSphericalRatio {ι : Type u} [Fintype ι] (B : FusionBasis ι)
    (J Jpos : PivotalData B) (hJ : J.Spherical) (hJpos : Jpos.Spherical)
    (χ : ι → ℂ) (hχ_eq : ∀ x, J.jdim x = χ x * Jpos.jdim x)
    (hχ_mul : ∀ x y z, 0 < B.N x y z → χ z = χ x * χ y)
    (hχ_ne : ∀ x, χ x ≠ 0) : SignCharacter B where
  val := χ
  val_tensor := hχ_mul
  val_mem := by
    apply sign_character_values χ hχ_ne
    · intro x
      have hone : χ B.one = 1 := by
        have := hχ_eq B.one
        rw [J.jdim_one, Jpos.jdim_one, mul_one] at this
        exact this.symm
      exact chi_dual_inv χ hone hχ_ne hχ_mul x
    · intro x
      have hx := hχ_eq x
      have hd := hχ_eq (B.dual x)
      have hsJ : J.jdim x = J.jdim (B.dual x) :=
        (J.spherical_iff_jdim_dual.mp hJ) x
      have hsP : Jpos.jdim x = Jpos.jdim (B.dual x) :=
        (Jpos.spherical_iff_jdim_dual.mp hJpos) x
      have hp : Jpos.jdim x ≠ 0 := Jpos.jdim_ne_zero x
      have hchain : χ x * Jpos.jdim x = χ (B.dual x) * Jpos.jdim x := by
        calc χ x * Jpos.jdim x = J.jdim x := hx.symm
          _ = J.jdim (B.dual x) := hsJ
          _ = χ (B.dual x) * Jpos.jdim (B.dual x) := hd
          _ = χ (B.dual x) * Jpos.jdim x := by rw [hsP]
      exact (mul_right_cancel₀ hp hchain).symm
  val_one := by
    have := hχ_eq B.one
    rw [J.jdim_one, Jpos.jdim_one, mul_one] at this
    exact this.symm
  val_dual := by
    intro x
    have hone : χ B.one = 1 := by
      have := hχ_eq B.one
      rw [J.jdim_one, Jpos.jdim_one, mul_one] at this
      exact this.symm
    exact chi_dual_inv χ hone hχ_ne hχ_mul x

/-- `sign_character_values` specialized to the ratio of two spherical
structures: every value of `χ = j / j⁺` lies in `{1,-1}`. -/
theorem sign_character_values_of_ratio {ι : Type u} [Fintype ι]
    {B : FusionBasis ι} (J Jpos : PivotalData B) (hJ : J.Spherical)
    (hJpos : Jpos.Spherical) (χ : ι → ℂ)
    (hχ_eq : ∀ x, J.jdim x = χ x * Jpos.jdim x)
    (hχ_mul : ∀ x y z, 0 < B.N x y z → χ z = χ x * χ y)
    (hχ_ne : ∀ x, χ x ≠ 0) :
    ∀ x, χ x = 1 ∨ χ x = -1 :=
  (SignCharacter.ofSphericalRatio B J Jpos hJ hJpos χ hχ_eq hχ_mul hχ_ne).val_mem

/-- Ratio `χ_X = j_X / j⁺_X` is self-dual when both structures are spherical. -/
theorem pivotalRatio_dual_of_spherical {ι : Type u} [Fintype ι]
    {B : FusionBasis ι} (J Jpos : PivotalData B) (hJ : J.Spherical)
    (hJpos : Jpos.Spherical) (x : ι) :
    pivotalRatio J Jpos (B.dual x) = pivotalRatio J Jpos x := by
  simp only [pivotalRatio]
  rw [J.jdim_dual_of_spherical hJ, Jpos.jdim_dual_of_spherical hJpos]

/-! ## Equation (3.5): `χ_ε = -1` -/

/-- **`chi_epsilon_eq_neg_one`.**  Paper (3.5): the inherited dimension of the
order-two lift `ε = (1,-id)` is `-1`, while the canonical positive structure
assigns `+1` to an invertible object; hence `χ_ε = j_ε / j⁺_ε = -1`. -/
theorem chi_epsilon_eq_neg_one {ι : Type u} [Fintype ι]
    (χ jdim jpos : ι → ℂ) (ε : ι)
    (h_eq : ∀ x, jdim x = χ x * jpos x)
    (h_eps : jdim ε = -1) (h_pos : jpos ε = 1) :
    χ ε = -1 := by
  have h := h_eq ε
  rw [h_eps, h_pos] at h
  -- `h : -1 = χ ε * 1`
  rw [mul_one] at h
  exact h.symm

/-- Same statement for a spherical comparison of pivotal dimensions. -/
theorem chi_epsilon_eq_neg_one_of_ratio {ι : Type u} [Fintype ι]
    {B : FusionBasis ι} (J Jpos : PivotalData B) (χ : ι → ℂ) (ε : ι)
    (h_eq : ∀ x, J.jdim x = χ x * Jpos.jdim x)
    (h_eps : J.jdim ε = -1) (h_pos : Jpos.jdim ε = 1) :
    χ ε = -1 :=
  chi_epsilon_eq_neg_one χ J.jdim Jpos.jdim ε h_eq h_eps h_pos

/-- Using `pivotalRatio` directly: `χ_ε = -1` when `j_ε = -1` and `j⁺_ε = 1`. -/
theorem pivotalRatio_eps_neg_one {ι : Type u} [Fintype ι]
    {B : FusionBasis ι} (J Jpos : PivotalData B) (ε : ι)
    (h_eps : J.jdim ε = -1) (h_pos : Jpos.jdim ε = 1) :
    pivotalRatio J Jpos ε = -1 := by
  simp only [pivotalRatio, h_eps, h_pos]
  field_simp

/-! ## Case 1: `χ|_ℰ = 1` (paper §3, Case 1) -/

/-- **`case1_integrality`.**  Paper Case 1: the `ℤ/2`-grading of `𝒬 = 𝒦_G` by
monodromy with the image `e` of `ε` has integral even part `e'_𝒬 = (𝒟̂₀)_G`, and
tensoring with the invertible `a` (monodromy partner of the descended `χ`)
bijects even and odd simples while preserving FP dimension.  Both components
are therefore integral, so `𝒬` is integral; Lemma 3.1 equivariantization then
gives `𝒦 ≅ 𝒬^G` integral. -/
theorem case1_integrality {ι : Type u} [Fintype ι] (B : FusionBasis ι)
    (G : Z2Grading B)
    (h_even : ∀ x ∈ G.even, ∃ n : ℤ, B.fpdim x = n)
    (flip : ι → ι)
    (_hflip : Function.Bijective flip)
    (_hflip_even_odd : ∀ x, x ∈ G.even → flip x ∈ G.odd)
    (hflip_odd_even : ∀ x, x ∈ G.odd → flip x ∈ G.even)
    (hflip_fp : ∀ x, B.fpdim (flip x) = B.fpdim x) :
    B.Integral := by
  intro x
  by_cases hx : x ∈ G.even
  · exact h_even x hx
  · have hxodd : x ∈ G.odd := by
      have hcover : x ∈ G.even ∪ G.odd := by
        rw [G.even_union_odd]
        trivial
      exact (Set.mem_union x G.even G.odd).mp hcover |>.resolve_left hx
    obtain ⟨n, hn⟩ := h_even (flip x) (hflip_odd_even x hxodd)
    refine ⟨n, ?_⟩
    rw [← hflip_fp x]
    exact hn

/-- Case 1 conclusion on the centralizer `𝒦 = ℬ'_𝒩`: integral.  The transfer
`𝒬` integral `⇒ 𝒦 ≅ 𝒬^G` integral is Lemma 3.1 (equivariantization), recorded
as an explicit hypothesis since group actions are outside the interface. -/
theorem case1_centralizer_integral {ι κ : Type u} [Fintype ι] [Fintype κ]
    (B : FusionBasis ι) (Q : FusionBasis κ) (G : Z2Grading Q)
    (h_even : ∀ x ∈ G.even, ∃ n : ℤ, Q.fpdim x = n)
    (flip : κ → κ) (hflip : Function.Bijective flip)
    (hflip_even_odd : ∀ x, x ∈ G.even → flip x ∈ G.odd)
    (hflip_odd_even : ∀ x, x ∈ G.odd → flip x ∈ G.even)
    (hflip_fp : ∀ x, Q.fpdim (flip x) = Q.fpdim x)
    (h_eqv : Q.Integral → B.Integral) :
    B.Integral :=
  h_eqv (case1_integrality Q G h_even flip hflip hflip_even_odd hflip_odd_even
    hflip_fp)

/-! ## Case 2: `χ|_ℰ ≠ 1` (paper §3, Case 2) -/

/-- **`case2_centralizer_dim`.**  Paper (3.6): with `𝒦₊ = ker χ` of index two
and `ℰ₊ = ℰ ∩ 𝒦₊` of index two, the centralizer-dimension formula for a
possibly degenerate braided category gives
`FPdim((𝒦₊)'_𝒦) = FPdim(𝒦) FPdim(ℰ₊) / FPdim(𝒦₊) = FPdim(ℰ)`. -/
theorem case2_centralizer_dim (FPdimK FPdimE : ℝ) (hK : FPdimK ≠ 0) :
    BraidedData.centralizerFPdim FPdimK (FPdimE / 2) (FPdimK / 2) = FPdimE :=
  BraidedData.centralizerFPdim_indexTwo FPdimK FPdimE hK

/-- The scalar identity behind (3.6) in raw arithmetic form. -/
theorem case2_centralizer_dim' (FPdimK FPdimE : ℝ) (hK : FPdimK ≠ 0) :
    FPdimK * (FPdimE / 2) / (FPdimK / 2) = FPdimE := by
  have h := case2_centralizer_dim FPdimK FPdimE hK
  simpa [BraidedData.centralizerFPdim] using h

/-- Müger center of the subcategory `𝒦₊`: simples of `𝒦₊` centralizing `𝒦₊`.
Combinatorially this is `C.centralizer Kplus ∩ Kplus`. -/
def mugerOfSub {ι : Type u} [Fintype ι] {B : FusionBasis ι}
    (C : BraidedData B) (Kplus : Set ι) : Set ι :=
  C.centralizer Kplus ∩ Kplus

/-- If `ℰ ⊆ (𝒦₊)'_𝒦` and the two subcategories have the same total FP
dimension, then `(𝒦₊)'_𝒦 = ℰ` and `Z₂(𝒦₊) = ℰ₊ = ℰ ∩ 𝒦₊`, as in (3.6). -/
theorem case2_centralizer_eq {ι : Type u} [Fintype ι]
    {B : FusionBasis ι} (C : BraidedData B) (Kplus E : Set ι)
    (hE_sub : E ⊆ C.centralizer Kplus)
    (hfp : B.subFPdim (C.centralizer Kplus) = B.subFPdim E) :
    C.centralizer Kplus = E ∧
      mugerOfSub C Kplus = E ∩ Kplus := by
  have h_eq : E = C.centralizer Kplus :=
    eq_of_subset_subFPdim hE_sub hfp.symm
  refine ⟨h_eq.symm, ?_⟩
  simp only [mugerOfSub]
  rw [← h_eq]

/-- **`case2_D_integrality`**, dimension part — equation (3.10):
`FPdim(ℰ ∨ ℐ^rev) = FPdim(ℰ) FPdim(ℐ) / FPdim(ℰ₊) = 2 FPdim(ℐ)`. -/
theorem case2_D_fpdim (FPdimE FPdimI FPdimEPlus : ℝ)
    (hE : FPdimE = 2 * FPdimEPlus) (hne : FPdimEPlus ≠ 0) :
    FPdimE * FPdimI / FPdimEPlus = 2 * FPdimI := by
  rw [hE]
  exact join_dim_eq_2I FPdimI FPdimEPlus hne

/-- The algebraic integrality step in Case 2. Dominance does not imply that
a target simple has dimension equal to a product of two source-simple
dimensions; it gives a constituent of such an image. Lemma 3.1 supplies
the required integrality without that invalid factorization shortcut. -/
theorem case2_D_integrality {ι ιE ιI : Type u}
    [Fintype ι] [Fintype ιE] [Fintype ιI]
    (D : FusionBasis ι) (E : FusionBasis ιE) (I : FusionBasis ιI)
    (hE : E.Integral) (hI : I.Integral)
    (F : FusionMap (E.prod I) D) : D.Integral :=
  lemma3_1_dominant F (E.prod_integral I hE hI)

/-- The Case 2 dimension arithmetic and the proved dominant-functor step. -/
theorem case2_D_integrality_with_dim {ι ιE ιI : Type u}
    [Fintype ι] [Fintype ιE] [Fintype ιI]
    (D : FusionBasis ι) (E : FusionBasis ιE) (I : FusionBasis ιI)
    (hE : E.Integral) (hI : I.Integral)
    (F : FusionMap (E.prod I) D)
    (FPdimE FPdimI FPdimEPlus : ℝ)
    (hEdim : FPdimE = 2 * FPdimEPlus) (hne : FPdimEPlus ≠ 0) :
    D.Integral ∧ FPdimE * FPdimI / FPdimEPlus = 2 * FPdimI :=
  ⟨case2_D_integrality D E I hE hI F,
    case2_D_fpdim FPdimE FPdimI FPdimEPlus hEdim hne⟩

/-! ## Packaging: `ModExt` and `GMEData` -/

/-- Combinatorial modular extension: a nondegenerate braided spherical ambient
fusion basis `𝒩` with a fully embedded premodular subbasis `𝒜` (injective on
simples, FP-dimension and monodromy preserving) and the centralizer of its
image. -/
structure ModExt (ι κ : Type u) [Fintype ι] [Fintype κ] where
  /-- Basis of the premodular subcategory. -/
  A : FusionBasis ι
  /-- Braiding on the subcategory. -/
  A_br : BraidedData A
  /-- Specified spherical structure on the subcategory. -/
  A_j : PivotalData A
  A_spherical : A_j.Spherical
  /-- Basis of the ambient modular category. -/
  N : FusionBasis κ
  /-- Braiding on the ambient category. -/
  N_br : BraidedData N
  /-- Spherical structure on the ambient category. -/
  N_j : PivotalData N
  N_spherical : N_j.Spherical
  N_nondeg : N_br.Nondegenerate
  /-- Fully faithful embedding on simples. -/
  incl : ι → κ
  incl_inj : Function.Injective incl
  incl_fpdim : ∀ x, N.fpdim (incl x) = A.fpdim x
  incl_monodromy : ∀ x y, N_br.monodromy (incl x) (incl y) = A_br.monodromy x y
  incl_jdim : ∀ x, N_j.jdim (incl x) = A_j.jdim x
  /-- Centralizer `𝒜'_𝒩` of the image. -/
  centralizer : Set κ
  centralizer_def : centralizer = N_br.centralizer (Set.range incl)

namespace ModExt

variable {ι κ : Type u} [Fintype ι] [Fintype κ] (E : ModExt ι κ)

/-- The extension has *integral centralizer* when every simple of `𝒜'_𝒩` has
integer FP dimension. -/
def CentralizerIntegral : Prop :=
  ∀ y ∈ E.centralizer, ∃ n : ℤ, E.N.fpdim y = n

/-- The extension is *weakly integral* when the total FP dimension of the
centralizer is an integer. -/
def CentralizerWeaklyIntegral : Prop :=
  ∃ N : ℤ, E.N.subFPdim E.centralizer = N

end ModExt

/-- **`GMEData`.**  Combinatorial data of the centralizer `𝒦 = ℬ'_𝒩` in the
proof of Theorem 1.1 (equations (3.3)–(3.5)): fusion basis of `𝒦`, its
braiding, the inherited spherical structure `j` (from `𝒩`), the canonical
positive spherical structure `j⁺` (ENO), the sign character `χ` with
`j = j⁺ χ`, the Tannakian Müger center `ℰ ≅ Rep(G)`, and the order-two object
`ε` with `dim ε = -1`. -/
structure GMEData (ι : Type u) [Fintype ι] where
  /-- Fusion basis of `𝒦 = ℬ'_𝒩`. -/
  B : FusionBasis ι
  /-- Braiding on `𝒦`. -/
  C : BraidedData B
  /-- Inherited spherical structure on `𝒦`. -/
  jInherited : PivotalData B
  /-- Canonical positive spherical structure (ENO). -/
  jPositive : PivotalData B
  /-- Sign character values of (3.4). -/
  chi : ι → ℂ
  /-- Tannakian Müger center `ℰ = Z₂(𝒦) = Z₂(ℬ) ≅ Rep(G)`, as a full
  fusion subcategory. -/
  E : Set ι
  /-- Order-two object `ε` with inherited dimension `-1`. -/
  epsilon : ι
  inherited_spherical : jInherited.Spherical
  positive_spherical : jPositive.Spherical
  /-- Equation (3.4): `j = j⁺ χ` on pivotal dimensions. -/
  jdim_eq : ∀ x, jInherited.jdim x = chi x * jPositive.jdim x
  /-- `χ` is a tensor automorphism of the identity. -/
  chi_mul : ∀ x y z, 0 < B.N x y z → chi z = chi x * chi y
  chi_ne_zero : ∀ x, chi x ≠ 0
  /-- The center is the Müger center of `𝒦`. -/
  E_eq_muger : E = C.mugerCenter
  /-- `ℰ` is a full fusion subcategory. -/
  E_full : BraidedData.IsFullSubcategory (B := B) E
  /-- `ℰ ≅ Rep(G)` is integral (representation dimensions). -/
  E_integral : ∀ x ∈ E, ∃ n : ℤ, B.fpdim x = n
  /-- `ε` is invertible and self-dual (order two). -/
  eps_invertible : B.IsInvertible epsilon
  eps_self_dual : B.dual epsilon = epsilon
  /-- Inherited dimension of the lift `ε = (1,-id)` is `-1`. -/
  jdim_eps : jInherited.jdim epsilon = -1
  /-- Positive dimension of the invertible object `ε` is `+1`. -/
  jdim_pos_eps : jPositive.jdim epsilon = 1
  /-- Total FP dimension of `𝒦` (equation (3.3): `FPdim(𝒦) = 4 FPdim(𝒟₀)`). -/
  dim_K : ℝ
  /-- Total FP dimension of `𝒟₀ = ℬ'_{ℳ₀}`. -/
  dim_D0 : ℝ
  dim_K_eq : dim_K = 4 * dim_D0
  dim_K_ne_zero : dim_K ≠ 0

namespace GMEData

variable {ι : Type u} [Fintype ι] (D : GMEData ι)

/-- Restrict the based data to the given fusion-closed center. -/
def centerBasis : FusionBasis D.E :=
  D.B.restrict D.E D.E_full.1 D.E_full.2.1 D.E_full.2.2

lemma center_integral : D.centerBasis.Integral := by
  intro x
  exact D.E_integral x x.property

/-- The sign character `χ` of (3.4) as a `SignCharacter`. -/
def sign : SignCharacter D.B :=
  SignCharacter.ofSphericalRatio D.B D.jInherited D.jPositive
    D.inherited_spherical D.positive_spherical D.chi D.jdim_eq D.chi_mul
    D.chi_ne_zero

/-- Paper (3.4): every value of `χ` is `±1`. -/
theorem sign_character_values (x : ι) : D.chi x = 1 ∨ D.chi x = -1 :=
  (D.sign).val_mem x

/-- Paper (3.5): `χ_ε = -1`. -/
theorem chi_epsilon_eq_neg_one : D.chi D.epsilon = -1 :=
  chi_epsilon_eq_neg_one_of_ratio D.jInherited D.jPositive D.chi D.epsilon
    D.jdim_eq D.jdim_eps D.jdim_pos_eps

/-- `χ` takes value `-1` on the order-two object `ε`. -/
theorem chi_eps_neg : D.chi D.epsilon = -1 := D.chi_epsilon_eq_neg_one

/-- The kernel `𝒦₊ = ker χ` (simples with `χ = +1`). -/
def ker : Set ι := {x | D.chi x = 1}

lemma one_mem_ker : D.B.one ∈ D.ker := by
  show D.chi D.B.one = 1
  have := (D.sign).val_one
  simpa using this

/-- When `χ` is trivial on `ℰ`, Case 1 applies. -/
def ChiTrivialOnE : Prop := ∀ x ∈ D.E, D.chi x = 1

/-- When `χ` is nontrivial on `ℰ`, Case 2 applies (`ℰ₊ = ℰ ∩ 𝒦₊` has index 2). -/
def ChiNontrivialOnE : Prop := ¬ ∀ x ∈ D.E, D.chi x = 1

/-- The classical dichotomy governing the construction. -/
theorem chi_dichotomy : D.ChiTrivialOnE ∨ D.ChiNontrivialOnE :=
  Classical.em _

/-- Under Case 1, `ε ∉ ℰ` (since `χ_ε = -1`). -/
theorem epsilon_not_mem_E_of_trivial (h : D.ChiTrivialOnE) : D.epsilon ∉ D.E := by
  intro hx
  have := h D.epsilon hx
  rw [D.chi_epsilon_eq_neg_one] at this
  exact absurd this (by norm_num)

end GMEData

/-! ## Auxiliary data of the two cases -/

/-- Data of Case 1 (`χ|_ℰ = 1`): the de-equivariantization `𝒬 = 𝒦_G` with its
`ℤ/2`-grading by monodromy with `e`, integral even part `(𝒟̂₀)_G`, and the
FP-dimension-preserving flip given by tensoring with the invertible object `a`
realizing the descended `χ`.  The equivariantization transfer of Lemma 3.1 is
an explicit hypothesis. -/
structure Case1Data {ι : Type u} [Fintype ι] (g : GMEData ι) where
  /-- Basis of `𝒬 = 𝒦_G`. -/
  κQ : Type u
  kQ : Fintype κQ
  Q : FusionBasis κQ
  /-- `ℤ/2`-grading by monodromy with `e`. -/
  grading : Z2Grading Q
  /-- Even part `e'_𝒬 = (𝒟̂₀)_G` is integral (Lemma 3.1 applied to
  de-equivariantization). -/
  even_integral : ∀ x ∈ grading.even, ∃ n : ℤ, Q.fpdim x = n
  /-- Tensoring with the invertible `a`. -/
  flip : κQ → κQ
  flip_bijective : Function.Bijective flip
  flip_even_odd : ∀ x, x ∈ grading.even → flip x ∈ grading.odd
  flip_odd_even : ∀ x, x ∈ grading.odd → flip x ∈ grading.even
  flip_fpdim : ∀ x, Q.fpdim (flip x) = Q.fpdim x
  /-- The dominant forgetful tensor multiplicity map for `K ≃ Q^G`.
  Its actual categorical construction is separate. -/
  forgetful : FusionMap g.B Q

/-- Data of Case 2 (`χ|_ℰ ≠ 1`): the positive kernel `𝒦₊`, the pseudounitary
modular extension `𝒦₊ ↪ 𝒫` with integral centralizer `ℐ`, and the diagonal
condensation `ℳ = (𝒩 ⊠ 𝒫^rev)^0_L` whose centralizer `𝒟 = ℰ ∨ ℐ^rev` is
represented by dominant tensor-functor multiplicities. -/
structure Case2Data {ι : Type u} [Fintype ι] (g : GMEData ι) where
  /-- Index-two kernel `𝒦₊ = ker χ`. -/
  Kplus : Set ι
  Kplus_eq : Kplus = {x | g.chi x = 1}
  /-- `ℰ₊ = ℰ ∩ 𝒦₊` has index two in `ℰ`. -/
  Eplus : Set ι
  Eplus_eq : Eplus = g.E ∩ Kplus
  /-- `ℰ` is contained in `(𝒦₊)'_𝒦` (transparent elements centralize `𝒦₊`). -/
  E_subset_centralizer : g.E ⊆ g.C.centralizer Kplus
  /-- The two subcategories `(𝒦₊)'_𝒦` and `ℰ` have equal total FP dimension,
  the set-level form of the dimension identity (3.6). -/
  centralizer_fpdim : g.B.subFPdim (g.C.centralizer Kplus) = g.B.subFPdim g.E
  /-- Dimension data realizing (3.6): `FPdim(𝒦₊) = FPdim(𝒦)/2` and
  `FPdim(ℰ₊) = FPdim(ℰ)/2`. -/
  dim_E : ℝ
  dim_Eplus : ℝ
  dim_Kplus : ℝ
  dim_Eplus_eq : dim_Eplus = dim_E / 2
  dim_Kplus_eq : dim_Kplus = g.dim_K / 2
  /-- `FPdim(ℰ) ≠ 0`. -/
  dim_E_pos : dim_E ≠ 0
  /-- Basis of `ℐ = (𝒦₊)'_𝒫` (integral centralizer of the positive kernel). -/
  κI : Type u
  kI : Fintype κI
  I : FusionBasis κI
  /-- `ℐ` is integral ([JF] applied to the positive `𝒦₊`). -/
  I_integral : I.Integral
  /-- Basis of the condensed centralizer `𝒟 = ℰ ∨ ℐ^rev`. -/
  κD : Type u
  kD : Fintype κD
  Dc : FusionBasis κD
  /-- Multiplicity data of the dominant tensor-product functor. -/
  dominantTensor : FusionMap (g.centerBasis.prod I) Dc

namespace Case1Data

variable {ι : Type u} [Fintype ι] {g : GMEData ι}

/-- The type of simples of `𝒬` is finite. -/
instance instFintype (c : Case1Data g) : Fintype c.κQ := c.kQ

variable (c : Case1Data g)

/-- Case 1: `𝒬` is integral by FP-dimension preservation of the grading. -/
theorem Q_integral : c.Q.Integral :=
  case1_integrality c.Q c.grading c.even_integral c.flip c.flip_bijective
    c.flip_even_odd c.flip_odd_even c.flip_fpdim

/-- **`case1_integrality` conclusion:** `𝒦` is integral. -/
theorem K_integral (c : Case1Data g) : g.B.Integral :=
  c.forgetful.integral_iff.mpr c.Q_integral

end Case1Data

namespace Case2Data

variable {ι : Type u} [Fintype ι] {g : GMEData ι}

/-- The type of simples of `ℐ` is finite. -/
instance instFintypeI (c : Case2Data g) : Fintype c.κI := c.kI

/-- The type of simples of `𝒟` is finite. -/
instance instFintypeD (c : Case2Data g) : Fintype c.κD := c.kD

variable (c : Case2Data g)

/-- The centralizer dimension identity (3.6):
`FPdim(𝒦) · FPdim(ℰ₊) / FPdim(𝒦₊) = FPdim(ℰ)`. -/
theorem centralizer_dim :
    BraidedData.centralizerFPdim g.dim_K (c.dim_E / 2) c.dim_Kplus
      = c.dim_E := by
  rw [c.dim_Kplus_eq]
  exact case2_centralizer_dim g.dim_K c.dim_E g.dim_K_ne_zero

/-- Raw form of (3.6). -/
theorem centralizer_dim' :
    g.dim_K * (c.dim_E / 2) / c.dim_Kplus = c.dim_E := by
  rw [c.dim_Kplus_eq]
  exact case2_centralizer_dim' g.dim_K c.dim_E g.dim_K_ne_zero

/-- **`case2_centralizer_dim` conclusion**, equation (3.6):
`(𝒦₊)'_𝒦 = ℰ` and `Z₂(𝒦₊) = ℰ₊`. -/
theorem centralizer_eq_E :
    g.C.centralizer c.Kplus = g.E ∧
      mugerOfSub g.C c.Kplus = g.E ∩ c.Kplus :=
  case2_centralizer_eq g.C c.Kplus g.E c.E_subset_centralizer c.centralizer_fpdim

/-- Integrality of the supplied condensed-centralizer basis follows from
the dominant tensor functor out of the product of the integral center and
integral `I`, by the proved based-data form of Lemma 3.1. -/
theorem D_integral : c.Dc.Integral :=
  case2_D_integrality c.Dc g.centerBasis c.I g.center_integral c.I_integral
    c.dominantTensor

/-- Dimension identity (3.10): `FPdim(ℰ) FPdim(ℐ) / FPdim(ℰ₊) = 2 FPdim(ℐ)`. -/
theorem join_dim (FPdimI FPdimEPlus : ℝ) (hne : FPdimEPlus ≠ 0) :
    (2 * FPdimEPlus) * FPdimI / FPdimEPlus = 2 * FPdimI :=
  join_dim_eq_2I FPdimI FPdimEPlus hne

end Case2Data

/-! ## Theorem 1.1 -/

/-- External input [Johnson–Freyd, Prop. 2.3]: existence of a nondegenerate
braided extension `ℬ ↪ ℳ₀` whose centralizer `𝒟₀ = ℬ'_{ℳ₀}` is integral.
Historical external-input interface only; no inhabitant is constructed. -/
structure JFProp23 {ι : Type u} [Fintype ι] (B : FusionBasis ι) where
  /-- Simple objects of `ℳ₀`. -/
  κ0 : Type u
  k0 : Fintype κ0
  M0 : FusionBasis κ0
  M0_br : BraidedData M0
  M0_j : PivotalData M0
  incl0 : ι → κ0
  incl0_inj : Function.Injective incl0
  incl0_fpdim : ∀ x, M0.fpdim (incl0 x) = B.fpdim x
  nondeg0 : M0_br.Nondegenerate
  /-- Centralizer `𝒟₀ = ℬ'_{ℳ₀}`. -/
  D0 : Set κ0
  D0_def : D0 = M0_br.centralizer (Set.range incl0)
  /-- `𝒟₀` is integral. -/
  D0_integral : ∀ y ∈ D0, ∃ n : ℤ, M0.fpdim y = n

/-- External input [ENO, Props. 8.23–8.24]: `𝒦` is pseudounitary and carries a
canonical positive spherical structure `j⁺` with positive real dimensions.
Historical interface only; no pseudounitarity theorem is proved here. -/
def ENOPseudounitary {ι : Type u} [Fintype ι] (D : GMEData ι) : Prop :=
  D.jPositive.Spherical ∧
    (∀ x : ι, 0 < (D.jPositive.jdim x).re ∧ (D.jPositive.jdim x).im = 0)

/-- External input [Proposition 2.2]: the minimal modular extension
`ℳ̂₀ ↪ 𝒩` preserves the specified spherical structure.  Its combinatorial
shadow is the package `GMEData` (inherited `j`, `χ`, `ε` with `dim ε = -1`,
and equation (3.3)). -/
def Prop22Holds {ι : Type u} [Fintype ι] (D : GMEData ι) : Prop :=
  D.jInherited.Spherical ∧ D.jInherited.jdim D.epsilon = -1

/-- A conditional integrality reduction used by Theorem 1.1. The case
constructions must be supplied for the applicable sign restriction. This
statement does not construct a modular category or prove Theorem 1.1.
In particular it does not require both mutually exclusive sign hypotheses. -/
theorem theorem1_1_reduction {ι : Type u} [Fintype ι] (D : GMEData ι)
    (c1 : D.ChiTrivialOnE → Nonempty (Case1Data D))
    (c2 : D.ChiNontrivialOnE → Nonempty (Case2Data D)) :
    D.ChiTrivialOnE ∧ D.B.Integral ∨
      ∃ c : Case2Data D, D.ChiNontrivialOnE ∧ c.Dc.Integral := by
  rcases D.chi_dichotomy with h | h
  · obtain ⟨c⟩ := c1 h
    exact Or.inl ⟨h, c.K_integral⟩
  · obtain ⟨c⟩ := c2 h
    exact Or.inr ⟨c, h, c.D_integral⟩

/-- Integrality once the Case 1 construction has actually been supplied. -/
theorem theorem1_1_case1 {ι : Type u} [Fintype ι] (D : GMEData ι)
    (c1 : Case1Data D) : D.B.Integral := c1.K_integral

/-- Integrality once the Case 2 construction has actually been supplied. -/
theorem theorem1_1_case2 {ι : Type u} [Fintype ι] (D : GMEData ι)
    (c2 : Case2Data D) : c2.Dc.Integral := c2.D_integral

/-- Integrality-only projection of the conditional reduction. -/
theorem theorem1_1_reduction_integral {ι : Type u} [Fintype ι]
    (D : GMEData ι)
    (c1 : D.ChiTrivialOnE → Nonempty (Case1Data D))
    (c2 : D.ChiNontrivialOnE → Nonempty (Case2Data D)) :
    D.B.Integral ∨ ∃ c : Case2Data D, c.Dc.Integral := by
  rcases theorem1_1_reduction D c1 c2 with h | ⟨c, _, hc⟩
  · exact Or.inl h.2
  · exact Or.inr ⟨c, hc⟩

-- Axiom audit for Theorem 1.1 (only propext, Classical.choice, Quot.sound).
#print axioms Paper18.sign_character_values
#print axioms Paper18.chi_epsilon_eq_neg_one
#print axioms Paper18.case1_integrality
#print axioms Paper18.case2_centralizer_dim
#print axioms Paper18.case2_D_integrality
#print axioms Paper18.GMEData.chi_epsilon_eq_neg_one
#print axioms Paper18.GMEData.sign_character_values
#print axioms Paper18.Case1Data.K_integral
#print axioms Paper18.Case2Data.D_integral
#print axioms Paper18.Case2Data.centralizer_eq_E
#print axioms Paper18.theorem1_1_reduction
#print axioms Paper18.theorem1_1_reduction_integral

end Paper18
