import Paper23.GroupRingModule

/-! Degree-wise free group-ring bases of the ordered cubical chain groups. -/
namespace Paper23.Labels
open Cubical

abbrev CanonicalInDegree (q : ℕ) := {c : Canonical // degree c.val.val = q}

def relabelInDegree (p : S4) (q : ℕ) (c : CubeInDegree q) : CubeInDegree q :=
  ⟨relabel p c.val, (relabel_degree p c.val).trans c.property⟩

noncomputable def degreeCanonicalEquiv (q : ℕ) :
    CubeInDegree q ≃ CanonicalInDegree q × S4 where
  toFun c := ⟨⟨canonical c.val, (canonical_degree c.val).trans c.property⟩, assignment c.val⟩
  invFun x := ⟨relabel x.2 x.1.val.val, (relabel_degree x.2 x.1.val.val).trans x.1.property⟩
  left_inv c := by
    apply Subtype.ext
    exact reconstruct c.val
  right_inv x := by
    have hh := canonicalEquiv.apply_symm_apply (x.1.val, x.2)
    refine Prod.ext ?_ ?_
    · apply Subtype.ext
      exact congrArg Prod.fst hh
    · change assignment (relabel x.2 x.1.val.val) = x.2
      exact congrArg Prod.snd hh

noncomputable def curryDegreeCoefficients (q : ℕ) :
    ((CanonicalInDegree q × S4) →₀ ℤ) ≃ₗ[ℤ] (CanonicalInDegree q →₀ GroupRing) where
  toFun f := Finsupp.curry f
  invFun f := Finsupp.uncurry f
  left_inv := Finsupp.uncurry_curry
  right_inv := Finsupp.curry_uncurry
  map_add' f g := by ext c p; rfl
  map_smul' r f := by ext c p; rfl

noncomputable def degreeCoefficientEquiv (q : ℕ) :
    Chain q ≃ₗ[ℤ] (CanonicalInDegree q →₀ GroupRing) :=
  (Finsupp.domLCongr (degreeCanonicalEquiv q)).trans (curryDegreeCoefficients q)

noncomputable instance degreeGroupRingSMul (q : ℕ) : SMul GroupRing (Chain q) where
  smul r x := (degreeCoefficientEquiv q).symm (r • degreeCoefficientEquiv q x)

@[simp] theorem degreeCoefficientEquiv_smul (q : ℕ) (r : GroupRing) (x : Chain q) :
    degreeCoefficientEquiv q (r • x) = r • degreeCoefficientEquiv q x :=
  (degreeCoefficientEquiv q).apply_symm_apply _

noncomputable instance degreeGroupRingModule (q : ℕ) : Module GroupRing (Chain q) :=
  Function.Injective.module GroupRing (degreeCoefficientEquiv q).toAddMonoidHom
    (degreeCoefficientEquiv q).injective (degreeCoefficientEquiv_smul q)

/-- The actual degree-q integral cubical chain group is a free left Z[S4]-module
with one basis vector for each canonical q-cube. -/
noncomputable def degreeGroupRingEquiv (q : ℕ) :
    Chain q ≃ₗ[GroupRing] (CanonicalInDegree q →₀ GroupRing) where
  toFun := degreeCoefficientEquiv q
  invFun := (degreeCoefficientEquiv q).symm
  left_inv := (degreeCoefficientEquiv q).symm_apply_apply
  right_inv := (degreeCoefficientEquiv q).apply_symm_apply
  map_add' := (degreeCoefficientEquiv q).map_add
  map_smul' := degreeCoefficientEquiv_smul q

@[simp] theorem degreeCoefficientEquiv_single (q : ℕ) (c : CubeInDegree q) (n : ℤ) :
    degreeCoefficientEquiv q (Finsupp.single c n) =
      Finsupp.single ⟨canonical c.val, (canonical_degree c.val).trans c.property⟩
        (Finsupp.single (assignment c.val) n) := by
  simp [degreeCoefficientEquiv, Finsupp.domLCongr_single,
    curryDegreeCoefficients, degreeCanonicalEquiv, Finsupp.curry_single]

/-- Scalar multiplication by p is precisely relabelling by p also in each
homogeneous degree. -/
theorem degree_permutationBasis_smul_single (q : ℕ) (p : S4)
    (c : CubeInDegree q) (n : ℤ) :
    permutationBasis p • (Finsupp.single c n : Chain q) =
      Finsupp.single (relabelInDegree p q c) n := by
  apply (degreeCoefficientEquiv q).injective
  rw [degreeCoefficientEquiv_smul, degreeCoefficientEquiv_single,
    degreeCoefficientEquiv_single]
  simp [permutationBasis, relabelInDegree, canonical_relabel, assignment_relabel,
    Finsupp.smul_single, smul_eq_mul, MonoidAlgebra.single_mul_single]

/-- Flatten the proof fields of a valid degree-q cell. -/
def degreeBasisEquiv (q : ℕ) :
    {c : RawCube // IsCube c ∧ degree c = q} ≃ CubeInDegree q where
  toFun c := ⟨⟨c.val,c.property.1⟩,c.property.2⟩
  invFun c := ⟨c.val.val,c.val.property,c.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The supported ambient-chain and typed-free-chain presentations agree. -/
noncomputable def supportedChainEquiv (q : ℕ) : Chains q ≃ₗ[ℤ] Chain q :=
  (Finsupp.supportedEquivFinsupp {c : RawCube | IsCube c ∧ degree c = q}).trans
    (Finsupp.domLCongr (degreeBasisEquiv q))

end Paper23.Labels
