import Paper06.MatchingMarginals

open Real Set BigOperators
open scoped Classical

namespace Paper06.Matching

attribute [local instance] sitesDecidableEq

variable {R : Type*} [Fintype R] [Field R]

/-- The uniform one-site input-output law. -/
noncomputable def uniformSiteLaw : FinProb (R × R) where
  w _ := (Fintype.card R : ℝ) ^ (-2 : ℤ)
  nonneg _ := by positivity
  sum_eq_one := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul,
      Nat.cast_mul, zpow_neg, zpow_ofNat]
    have hc := card_ne_zero (R := R)
    field_simp

/-- Select one endpoint of a canonical edge. -/
def endpoint {Z : Type*} (b : Bool) (w : Z × Z) : Z := if b then w.2 else w.1

theorem edgeLaw_endpoint_mass (b : Bool) (a : R × R) :
    (∑ w : (R × R) × (R × R), (edgeLaw (R := R)).w w *
      (if endpoint b w = a then (1 : ℝ) else 0)) =
      (Fintype.card R : ℝ) ^ (-2 : ℤ) := by
  classical
  cases b
  · change (∑ w : (R × R) × (R × R), edgeW w.1 w.2 *
      (if w.1 = a then (1 : ℝ) else 0)) = _
    rw [Fintype.sum_prod_type]
    simp only [mul_ite, mul_one, mul_zero]
    simp
    exact edgeW_marginal a
  · change (∑ w : (R × R) × (R × R), edgeW w.1 w.2 *
      (if w.2 = a then (1 : ℝ) else 0)) = _
    rw [Fintype.sum_prod_type]
    simp only [mul_ite, mul_one, mul_zero]
    simp
    simp_rw [edgeW_symm]
    exact edgeW_marginal a

/-- Change of variables grouping the independent canonical edges. -/
theorem canonical_expect_edges (m : ℕ) (h : (Sites m → R × R) → ℝ) :
    (∑ z : Sites m → R × R, canonicalW m z * h z) =
      ∑ w : Fin m → (R × R) × (R × R),
        channelLambda (fun _ : Fin m => edgeLaw (R := R)) w *
          h ((groupEndpoints m (R × R)).symm w) := by
  apply Fintype.sum_equiv (groupEndpoints m (R × R))
  intro z
  rw [(groupEndpoints m (R × R)).symm_apply_apply]
  rfl

noncomputable def canonicalPairMass (m : ℕ) (i j : Sites m) (a b : R × R) : ℝ :=
  ∑ z : Sites m → R × R, canonicalW m z *
    (if z i = a ∧ z j = b then 1 else 0)

theorem canonicalPairMass_same (m : ℕ) (i j : Sites m)
    (hij : i ≠ j) (hsame : i.1 = j.1) (a b : R × R) :
    canonicalPairMass m i j a b = edgeW a b := by
  classical
  rcases i with ⟨c, u⟩
  rcases j with ⟨d, v⟩
  change c = d at hsame
  subst d
  unfold canonicalPairMass
  rw [canonical_expect_edges]
  cases u <;> cases v
  · exact (hij rfl).elim
  · change (∑ w : Fin m → (R × R) × (R × R),
      channelLambda (fun _ : Fin m => edgeLaw (R := R)) w *
        (if (w c).1 = a ∧ (w c).2 = b then 1 else 0)) = _
    rw [channelLambda_expect (fun _ : Fin m => edgeLaw (R := R)) c
      (fun w => if w.1 = a ∧ w.2 = b then 1 else 0)]
    change (∑ w : (R × R) × (R × R), edgeW w.1 w.2 *
      (if w.1 = a ∧ w.2 = b then 1 else 0)) = _
    rw [Fintype.sum_prod_type]
    simp [ite_and]
  · change (∑ w : Fin m → (R × R) × (R × R),
      channelLambda (fun _ : Fin m => edgeLaw (R := R)) w *
        (if (w c).2 = a ∧ (w c).1 = b then 1 else 0)) = _
    rw [channelLambda_expect (fun _ : Fin m => edgeLaw (R := R)) c
      (fun w => if w.2 = a ∧ w.1 = b then 1 else 0)]
    change (∑ w : (R × R) × (R × R), edgeW w.1 w.2 *
      (if w.2 = a ∧ w.1 = b then 1 else 0)) = _
    rw [Fintype.sum_prod_type]
    simpa [ite_and] using edgeW_symm b a
  · exact (hij rfl).elim

theorem canonicalPairMass_different (m : ℕ) (i j : Sites m)
    (hdiff : i.1 ≠ j.1) (a b : R × R) :
    canonicalPairMass m i j a b =
      (Fintype.card R : ℝ) ^ (-2 : ℤ) * (Fintype.card R : ℝ) ^ (-2 : ℤ) := by
  classical
  unfold canonicalPairMass
  rw [canonical_expect_edges]
  change (∑ w : Fin m → (R × R) × (R × R),
    channelLambda (fun _ : Fin m => edgeLaw (R := R)) w *
      (if endpoint i.2 (w i.1) = a ∧ endpoint j.2 (w j.1) = b then 1 else 0)) = _
  rw [channelLambda_pair_expect (fun _ : Fin m => edgeLaw (R := R)) hdiff
    (fun u v => if endpoint i.2 u = a ∧ endpoint j.2 v = b then 1 else 0)]
  have ht : ∀ u v : (R × R) × (R × R),
      (edgeLaw (R := R)).w u * (edgeLaw (R := R)).w v *
        (if endpoint i.2 u = a ∧ endpoint j.2 v = b then 1 else 0) =
      ((edgeLaw (R := R)).w u * (if endpoint i.2 u = a then 1 else 0)) *
        ((edgeLaw (R := R)).w v * (if endpoint j.2 v = b then 1 else 0)) := by
    intro u v
    by_cases hu : endpoint i.2 u = a <;> by_cases hv : endpoint j.2 v = b <;>
      simp [hu, hv]
  simp_rw [ht]
  rw [← Finset.sum_mul_sum]
  rw [edgeLaw_endpoint_mass, edgeLaw_endpoint_mass]

theorem canonicalPairMass_formula (m : ℕ) (i j : Sites m) (hij : i ≠ j)
    (a b : R × R) :
    canonicalPairMass m i j a b =
      if i.1 = j.1 then edgeW a b else
        (Fintype.card R : ℝ) ^ (-2 : ℤ) * (Fintype.card R : ℝ) ^ (-2 : ℤ) := by
  by_cases h : i.1 = j.1
  · rw [if_pos h, canonicalPairMass_same m i j hij h]
  · rw [if_neg h, canonicalPairMass_different m i j h]

/-- A bijective coordinate relabelling transports the literal two-point
marginal by the inverse labels. -/
theorem reindex_pair_mass {κ ι α : Type*} [Fintype κ] [Fintype ι] [Fintype α]
    [DecidableEq κ] [DecidableEq ι] (e : κ ≃ ι) (P : FinProb (κ → α))
    (i j : ι) (a b : α) :
    (FinProb.map (reindexLaw e P) (fun z => (z i, z j))).w (a, b) =
      (FinProb.map P (fun z => (z (e.symm i), z (e.symm j)))).w (a, b) := by
  classical
  let ee : (ι → α) ≃ (κ → α) :=
    { toFun := fun z => z ∘ e
      invFun := fun z => z ∘ e.symm
      left_inv := by intro z; funext c; simp
      right_inv := by intro z; funext c; simp }
  simp only [FinProb.map_w]
  apply Fintype.sum_equiv ee
  intro z
  have hi : (ee z) (e.symm i) = z i := by simp [ee]
  have hj : (ee z) (e.symm j) = z j := by simp [ee]
  simp only [hi, hj]
  split_ifs <;> rfl

theorem conditional_pair_mass (m : ℕ) (σ : Equiv.Perm (Sites m))
    (i j : Sites m) (a b : R × R) :
    (FinProb.map (conditionalMatchingLaw m σ) (fun z => (z i, z j))).w (a, b) =
      canonicalPairMass m (σ.symm i) (σ.symm j) a b := by
  classical
  unfold conditionalMatchingLaw
  rw [reindex_pair_mass]
  unfold canonicalPairMass
  simp only [FinProb.map_w, Prod.mk.injEq]
  apply Finset.sum_congr rfl
  intro z _
  split_ifs <;> simp

theorem sameEdge_iff_flip (m : ℕ) (i j : Sites m) (hij : i ≠ j) :
    i.1 = j.1 ↔ flipEndpoint m i = j := by
  rcases i with ⟨c, u⟩
  rcases j with ⟨d, v⟩
  cases u <;> cases v <;> simp_all [flipEndpoint, Prod.mk.injEq]

theorem sameEdge_iff_partner (m : ℕ) (σ : Equiv.Perm (Sites m))
    (i j : Sites m) (hij : i ≠ j) :
    (σ.symm i).1 = (σ.symm j).1 ↔ partner m σ i = j := by
  rw [sameEdge_iff_flip m (σ.symm i) (σ.symm j) (fun h => hij (σ.symm.injective h))]
  constructor
  · intro h
    unfold partner
    rw [h, σ.apply_symm_apply]
  · intro h
    apply σ.injective
    simpa only [partner, Equiv.apply_symm_apply] using h

/-- Conditional on a matching, two distinct sites either share the CHSH
edge law or belong to independent edges and have uniform product law. -/
theorem conditional_pair_formula (m : ℕ) (σ : Equiv.Perm (Sites m))
    (i j : Sites m) (hij : i ≠ j) (a b : R × R) :
    (FinProb.map (conditionalMatchingLaw m σ) (fun z => (z i, z j))).w (a, b) =
      if partner m σ i = j then edgeW a b else
        (Fintype.card R : ℝ) ^ (-2 : ℤ) * (Fintype.card R : ℝ) ^ (-2 : ℤ) := by
  rw [conditional_pair_mass, canonicalPairMass_formula m (σ.symm i) (σ.symm j)
    (fun h => hij (σ.symm.injective h))]
  simp only [sameEdge_iff_partner m σ i j hij]

theorem matching_pair_average (m : ℕ) (i j : Sites m) (a b : R × R) :
    (FinProb.map (matchingLaw m) (fun z => (z i, z j))).w (a, b) =
      (Fintype.card (Equiv.Perm (Sites m)) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Sites m),
          (FinProb.map (conditionalMatchingLaw m σ) (fun z => (z i, z j))).w (a, b) := by
  exact matching_eventMass_average m (fun z => (z i, z j) = (a, b))

theorem matching_pair_mass_inv (m : ℕ) (i j : Sites m) (hij : i ≠ j)
    (a b : R × R) :
    (FinProb.map (matchingLaw m) (fun z => (z i, z j))).w (a, b) =
      ((Fintype.card (Sites m) : ℝ) - 1)⁻¹ * edgeW a b +
        (1 - ((Fintype.card (Sites m) : ℝ) - 1)⁻¹) *
          ((Fintype.card R : ℝ) ^ (-2 : ℤ) * (Fintype.card R : ℝ) ^ (-2 : ℤ)) := by
  classical
  rw [matching_pair_average]
  simp_rw [conditional_pair_formula m _ i j hij]
  let A : ℝ := edgeW a b
  let B : ℝ := (Fintype.card R : ℝ) ^ (-2 : ℤ) * (Fintype.card R : ℝ) ^ (-2 : ℤ)
  let C : ℝ := Fintype.card (Equiv.Perm (Sites m))
  have ht : ∀ σ : Equiv.Perm (Sites m),
      (if partner m σ i = j then A else B) =
        (if partner m σ i = j then (1 : ℝ) else 0) * (A - B) + B := by
    intro σ
    by_cases h : partner m σ i = j <;> simp [h]
  change C⁻¹ * (∑ σ : Equiv.Perm (Sites m), if partner m σ i = j then A else B) = _
  rw [Finset.sum_congr rfl (fun σ _ => ht σ), Finset.sum_add_distrib, ← Finset.sum_mul]
  have hC : C⁻¹ * C = 1 := by
    exact inv_mul_cancel₀ (by dsimp [C]; exact_mod_cast
      (ne_of_gt (Fintype.card_pos : 0 < Fintype.card (Equiv.Perm (Sites m)))))
  have hp : C⁻¹ * (∑ σ : Equiv.Perm (Sites m),
      if partner m σ i = j then (1 : ℝ) else 0) =
      ((Fintype.card (Sites m) : ℝ) - 1)⁻¹ :=
    partner_probability (flipEndpoint m) (flipEndpoint_ne m) i j hij
  rw [mul_add, ← mul_assoc, hp]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  change _ + C⁻¹ * (C * B) = _
  rw [← mul_assoc, hC]
  dsimp [A, B]
  ring

/-- Equation (10), pointwise for the actual two-coordinate marginal of
the single `n`-site matching law, with normalized edge and uniform laws. -/
theorem matchingLawFin_pair_mass (n : ℕ) (hEven : Even n) (hn2 : 2 ≤ n)
    (i j : Fin n) (hij : i ≠ j) (a b : R × R) :
    (FinProb.map (matchingLawFin (R := R) n hEven) (fun z => (z i, z j))).w (a, b) =
      (1 / ((n : ℝ) - 1)) * (edgeLaw (R := R)).w (a, b) +
        (((n : ℝ) - 2) / ((n : ℝ) - 1)) *
          (prod (uniformSiteLaw (R := R)) (uniformSiteLaw (R := R))).w (a, b) := by
  unfold matchingLawFin matchingLawAlong
  rw [reindex_pair_mass]
  rw [matching_pair_mass_inv (n / 2) _ _
    (fun h => hij ((evenSitesEquiv n hEven).symm.injective h))]
  have hc : Fintype.card (Sites (n / 2)) = n := by
    simpa only [Fintype.card_fin] using Fintype.card_congr (evenSitesEquiv n hEven)
  rw [hc]
  change ((n : ℝ) - 1)⁻¹ * edgeW a b +
      (1 - ((n : ℝ) - 1)⁻¹) *
        ((Fintype.card R : ℝ) ^ (-2 : ℤ) * (Fintype.card R : ℝ) ^ (-2 : ℤ)) =
    (1 / ((n : ℝ) - 1)) * edgeW a b +
      (((n : ℝ) - 2) / ((n : ℝ) - 1)) *
        ((Fintype.card R : ℝ) ^ (-2 : ℤ) * (Fintype.card R : ℝ) ^ (-2 : ℤ))
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hd : (n : ℝ) - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- The normalized convex law on the right-hand side of equation (10). -/
noncomputable def twoPointMixture (n : ℕ) (hn2 : 2 ≤ n) :
    FinProb ((R × R) × (R × R)) :=
  mixture
    (fun b : Bool => if b then ((n : ℝ) - 2) / ((n : ℝ) - 1) else 1 / ((n : ℝ) - 1))
    (by
      intro b
      have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
      cases b <;> dsimp <;> apply div_nonneg <;> linarith)
    (by
      have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
      have hd : (n : ℝ) - 1 ≠ 0 := by linarith
      rw [Fintype.sum_bool]
      dsimp
      field_simp
      ring)
    (fun b : Bool => if b then prod (uniformSiteLaw (R := R)) uniformSiteLaw else edgeLaw)

/-- **Equation (10)** as literal equality of normalized probability laws.
This identifies the marginal of the already constructed extension; the
edge-mixture formula is derived from its actual matching probabilities. -/
theorem matchingLawFin_pair_eq (n : ℕ) (hEven : Even n) (hn2 : 2 ≤ n)
    (i j : Fin n) (hij : i ≠ j) :
    FinProb.map (matchingLawFin (R := R) n hEven) (fun z => (z i, z j)) =
      twoPointMixture (R := R) n hn2 := by
  apply FinProb.ext
  intro ab
  rw [matchingLawFin_pair_mass n hEven hn2 i j hij ab.1 ab.2]
  simp only [twoPointMixture, mixture, Fintype.sum_bool, Bool.false_eq_true,
    if_false, if_true]
  ring

end Paper06.Matching
