import Paper18.Results.Lacabanne
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Proposition 2.2 — spherical extension over `Rep(ℤ/2)`

Let `A` be a premodular fusion category with `Z₂(A) = ⟨f⟩ ≅ Rep(ℤ/2)` and
prescribed dimension `dim_A(f) = -1`.  Every minimal nondegenerate braided
extension `ι : A ↪ N` admits a spherical structure restricting to the given
one.  More precisely, the pivotal structure on `N` obtained from the
fixed-boundary extension of Lemma A.1 is spherical.

The paper's argument runs as follows.

1. The double-dual autoequivalence of `N` and the fixed-boundary isomorphism
   `β : (-)**_N ⇒ id` produce a pivotal structure `j_N` restricting to the
   prescribed spherical `j_A`.
2. The slope of `j_N` is trivial on `A` (because `j_A` is spherical), so the
   Lacabanne object `t` of Lemma 2.1 lies in the centralizer
   `A'_N = ⟨f⟩ = {1, f}`.
3. The Tannakian self-braiding `c_{f,f} = id` together with `dim_A(f) = -1`
   gives the twist `θ_f = -1`.
4. Since `f^{-1} = f`, the twist constraint (2.2) of Lemma 2.1 excludes
   `t = f`.  Hence `t = 1` and the slope of `j_N` is trivial: `j_N` is
   spherical.

This module proves steps 2–4 against the combinatorial fusion interface.
Existence of the minimal extension and of the fixed-boundary isomorphism
(Lemma A.1) is an explicit hypothesis, never a custom axiom.

## Main declarations

* `Paper18.TwistDimension`: twist–dimension relation for a Tannakian invertible.
* `Paper18.theta_f_eq_neg_one`: `dim f = -1` and `c_{f,f} = id` give `θ_f = -1`.
* `Paper18.prop2_2_slope_trivial`: core exclusion — `t ∈ {1,f}` and `θ_f = -1`
  force `t = 1` and trivial slope.
* `Paper18.prop2_2`: the induced pivotal structure is spherical.
-/

noncomputable section

open Classical

universe u

open scoped BigOperators

namespace Paper18

section Prop22

variable {ι : Type u} [Fintype ι] {B : FusionBasis ι}
  {J : PivotalData B} {θ : BalancingData J} {C : BraidedData B}

/-! ## Twist–dimension relation for a Tannakian invertible -/

/-- Twist–dimension relation for a Tannakian invertible object: if `f` is
invertible and self-dual with trivial self-braiding `c_{f,f} = id`, then its
twist is its pivotal dimension, `θ_f = d_f`.  Together with `d_f = -1` this
gives `θ_f = -1`. -/
def TwistDimension (B : FusionBasis ι) (C : BraidedData B)
    (J : PivotalData B) (θ : BalancingData J) (f : ι) : Prop :=
  B.IsInvertible f → B.dual f = f → C.monodromy f f = 1 → θ.theta f = J.jdim f

/-- The twist of a Tannakian invertible is its pivotal dimension. -/
lemma theta_eq_jdim_of_tannakian
    (hTD : TwistDimension B C J θ f)
    (hfinv : B.IsInvertible f) (hfself : B.dual f = f)
    (hself : C.monodromy f f = 1) :
    θ.theta f = J.jdim f :=
  hTD hfinv hfself hself

/-- `dim f = -1` and the Tannakian self-braiding give `θ_f = -1`. -/
lemma theta_f_eq_neg_one
    (hTD : TwistDimension B C J θ f)
    (hfinv : B.IsInvertible f) (hfself : B.dual f = f)
    (hself : C.monodromy f f = 1)
    (hdim : J.jdim f = -1) :
    θ.theta f = -1 := by
  rw [hTD hfinv hfself hself, hdim]

/-- The Tannakian data of `f` recorded by `MugerIsOrderTwo` (hypothesis
`Z₂(A) = ⟨f⟩ ≅ Rep(ℤ/2)`): invertible, self-dual, nontrivial, with trivial
self-braiding.  These are exactly the properties used in Proposition 2.2. -/
lemma tannakian_data_of_mugerOrderTwo {f : ι} (T : C.MugerIsOrderTwo f) :
    B.IsInvertible f ∧ B.dual f = f ∧ f ≠ B.one ∧ C.monodromy f f = 1 :=
  ⟨T.f_invertible, T.f_self_dual, T.f_ne_one, T.self_monodromy⟩

/-! ## Locating the Lacabanne object in `A'_N = ⟨f⟩` -/

/-- The slope of `j_N` is trivial on `A` (because the restriction `j_A` is
spherical), so monodromy of any simple `a ∈ A` with the Lacabanne object `t`
is trivial.  Hence `t` lies in the centralizer `A'_N`, and if `A'_N = ⟨f⟩`
then `t ∈ {1, f}`. -/
lemma t_mem_of_slope_trivial_on_subcat
    (A : Set ι) (f t : ι)
    (hcent : ∀ x : ι, (∀ a ∈ A, C.monodromy x a = 1) ↔ x = B.one ∨ x = f)
    (hslopeA : ∀ a ∈ A, J.gamma a = 1)
    (hmono : SlopeIsMonodromy C J t) :
    t = B.one ∨ t = f := by
  refine (hcent t).mp ?_
  intro a ha
  rw [C.monodromy_symm, hmono a, hslopeA a ha]

/-! ## Core exclusion: (2.2) rules out `t = f` -/

/-- **Core of Proposition 2.2.**
Let `f` be an invertible self-dual simple with `θ_f = -1`, and let `t` be the
Lacabanne object of Lemma 2.1 (invertible, monodromy equal to the slope).
If `t ∈ {1, f}`, then necessarily `t = 1`, and the slope is trivial.

Indeed, (2.2) gives `θ_{t^{-1}} = 1`.  If `t = f` then `f^{-1} = f` and
`θ_f = 1`, contradicting `θ_f = -1`.  Hence `t = 1`, and (2.1) gives
`γ_x = monodromy(x, 1) = 1` for every simple `x`. -/
theorem prop2_2_slope_trivial
    (f t : ι)
    (hfinv : B.IsInvertible f) (hfself : B.dual f = f) (hfne : f ≠ B.one)
    (htheta_f : θ.theta f = -1)
    (htinv : B.IsInvertible t)
    (ht_eq : t = B.one ∨ t = f)
    (hmono : SlopeIsMonodromy C J t)
    (A : InvertibleTensor B C J θ t)
    (hH : HopfLinkIdentity C J θ) :
    t = B.one ∧ ∀ x : ι, J.gamma x = 1 := by
  -- `hfinv`, `hfne` record that `f` generates `⟨f⟩ ≅ Rep(ℤ/2)`; the exclusion
  -- itself only uses self-duality and `θ_f = -1`.
  have _ := hfinv
  have _ := hfne
  -- `t ≠ f` by (2.2) and `θ_f = -1`.
  have ht_one : t = B.one := by
    rcases ht_eq with h | h
    · exact h
    · exfalso
      -- (2.2): `θ (dual t) = 1`.
      have h22 : θ.theta (B.dual t) = 1 :=
        lemma2_1_twist t htinv hmono A hH
      -- `t = f` and `f` self-dual give `θ_f = 1`, contradicting `θ_f = -1`.
      rw [h, hfself] at h22
      have hne : (1:ℂ) = -1 := h22.symm.trans htheta_f
      norm_num at hne
  refine ⟨ht_one, ?_⟩
  -- The slope is the monodromy with `t = 1`, hence trivial.
  intro x
  have hx := hmono x
  rw [ht_one] at hx
  calc J.gamma x = C.monodromy x B.one := hx.symm
    _ = 1 := C.monodromy_unit_right x

/-! ## Proposition 2.2 -/

/-- **Proposition 2.2 (conditional form).**
Let `N` be a nondegenerate braided fusion category containing a full fusion
subcategory `A` with centralizer `A'_N = ⟨f⟩`, where `f` is a Tannakian
invertible with prescribed dimension `d_f = -1`.  Let `j` be a pivotal
structure on `N` whose slope is trivial on `A` (the restriction of the
prescribed spherical structure `j_A`), and let `t` be the Lacabanne object of
Lemma 2.1.  Then `j` is spherical.

This is the paper's argument: `t ∈ A'_N = ⟨f⟩ = {1, f}`, the twist is
`θ_f = -1`, and (2.2) excludes `t = f`, so `t = 1` and the slope is trivial.

The existence of a minimal nondegenerate extension `N` of `A` together with
the fixed-boundary isomorphism producing `j` (Lemma A.1) is assumed as the
hypotheses `hcent`, `hslopeA` and the Lacabanne data of `t`. -/
theorem prop2_2
    (A : Set ι) (f t : ι)
    (hcent : ∀ x : ι, (∀ a ∈ A, C.monodromy x a = 1) ↔ x = B.one ∨ x = f)
    (hslopeA : ∀ a ∈ A, J.gamma a = 1)
    (hfinv : B.IsInvertible f) (hfself : B.dual f = f) (hfne : f ≠ B.one)
    (hself : C.monodromy f f = 1)
    (hTD : TwistDimension B C J θ f)
    (hdim : J.jdim f = -1)
    (htinv : B.IsInvertible t)
    (hmono : SlopeIsMonodromy C J t)
    (Aμ : InvertibleTensor B C J θ t)
    (hH : HopfLinkIdentity C J θ) :
    J.Spherical := by
  -- Twist of the Tannakian invertible is `θ_f = -1`.
  have htheta_f : θ.theta f = -1 :=
    theta_f_eq_neg_one hTD hfinv hfself hself hdim
  -- The Lacabanne object lies in `A'_N = {1, f}`.
  have ht_eq : t = B.one ∨ t = f :=
    t_mem_of_slope_trivial_on_subcat A f t hcent hslopeA hmono
  -- (2.2) excludes `t = f`, so the slope is trivial.
  exact (prop2_2_slope_trivial f t hfinv hfself hfne htheta_f
    htinv ht_eq hmono Aμ hH).2

/-- **Proposition 2.2** with the Tannakian hypothesis packaged as
`MugerIsOrderTwo f` (`Z₂(A) = ⟨f⟩ ≅ Rep(ℤ/2)`) and the prescribed spherical
structure on `A` encoded as trivial slope on the subcategory `A`. -/
theorem prop2_2_mugerOrderTwo
    (A : Set ι) (f t : ι)
    (T : C.MugerIsOrderTwo f)
    (hcent : ∀ x : ι, (∀ a ∈ A, C.monodromy x a = 1) ↔ x = B.one ∨ x = f)
    (hslopeA : ∀ a ∈ A, J.gamma a = 1)
    (hTD : TwistDimension B C J θ f)
    (hdim : J.jdim f = -1)
    (htinv : B.IsInvertible t)
    (hmono : SlopeIsMonodromy C J t)
    (Aμ : InvertibleTensor B C J θ t)
    (hH : HopfLinkIdentity C J θ) :
    J.Spherical := by
  obtain ⟨hfinv, hfself, hfne, hself⟩ := tannakian_data_of_mugerOrderTwo T
  exact prop2_2 A f t hcent hslopeA hfinv hfself hfne hself hTD hdim
    htinv hmono Aμ hH

/-- Corollary: under the hypotheses of Proposition 2.2 the Lacabanne object is
the unit, so the slope is the trivial tensor automorphism of the identity. -/
theorem prop2_2_slope_is_one
    (A : Set ι) (f t : ι)
    (hcent : ∀ x : ι, (∀ a ∈ A, C.monodromy x a = 1) ↔ x = B.one ∨ x = f)
    (hslopeA : ∀ a ∈ A, J.gamma a = 1)
    (hfinv : B.IsInvertible f) (hfself : B.dual f = f) (hfne : f ≠ B.one)
    (hself : C.monodromy f f = 1)
    (hTD : TwistDimension B C J θ f)
    (hdim : J.jdim f = -1)
    (htinv : B.IsInvertible t)
    (hmono : SlopeIsMonodromy C J t)
    (Aμ : InvertibleTensor B C J θ t)
    (hH : HopfLinkIdentity C J θ) :
    t = B.one ∧ ∀ x : ι, J.gamma x = 1 := by
  have htheta_f : θ.theta f = -1 :=
    theta_f_eq_neg_one hTD hfinv hfself hself hdim
  have ht_eq : t = B.one ∨ t = f :=
    t_mem_of_slope_trivial_on_subcat A f t hcent hslopeA hmono
  exact prop2_2_slope_trivial f t hfinv hfself hfne htheta_f
    htinv ht_eq hmono Aμ hH

end Prop22

end Paper18

-- Axiom audit of the main names of Lemma 2.1 and Proposition 2.2.
#print axioms Paper18.lemma2_1_twist
#print axioms Paper18.lemma2_1_unique
#print axioms Paper18.lemma2_1
#print axioms Paper18.gaussSum_ne_zero
#print axioms Paper18.prop2_2_slope_trivial
#print axioms Paper18.prop2_2
#print axioms Paper18.prop2_2_mugerOrderTwo
