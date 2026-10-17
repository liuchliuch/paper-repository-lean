import Paper26.GraphFamily
import Paper26.TailGeometry
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Actual real Euclidean coordinates for complex graph parameters

Every entry of `Matrix (Fin s) (Fin r) ℂ` contributes its real and imaginary
parts.  An explicit product-of-`Fin` equivalence reindexes these coordinates
to `Fin (2*r*s)`.  The resulting real continuous linear equivalence has the
exact Euclidean squared norm equal to the actual matrix Frobenius square.
All topologies are the ordinary finite product topologies; no global matrix
norm instance is installed.

The measure statements use standard complex-entry product Lebesgue measure
and standard Euclidean volume.  They are coordinate-normalization results,
independent of graph priors, parameter-volume bounds, or losses.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder
open MeasureTheory

namespace Paper26.MatrixCoordinates

local instance matrixMeasurableSpace (m n : Type*) : MeasurableSpace (Matrix m n ℂ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℂ))

local instance matrixBorelSpace (m n : Type*) [Fintype m] [Fintype n] :
    BorelSpace (Matrix m n ℂ) :=
  inferInstanceAs (BorelSpace (m → n → ℂ))

/-- One real/imaginary tag for each actual complex matrix entry. -/
abbrev CoordinateIndex (r s : ℕ) := Fin s × (Fin r × Fin 2)

/-- Explicit row/column/tag enumeration of all `2*r*s` real coordinates. -/
def indexEquiv (r s : ℕ) : CoordinateIndex r s ≃ Fin (2 * r * s) :=
  ((Equiv.prodCongr (Equiv.refl (Fin s)) finProdFinEquiv).trans
    finProdFinEquiv).trans (finCongr (by ring))

/-- The real/imaginary tag varies fastest, then the column, then the row. -/
@[simp] theorem indexEquiv_val (r s : ℕ) (i : Fin s) (j : Fin r) (c : Fin 2) :
    (indexEquiv r s (i, j, c)).val = c.val + 2 * j.val + (r * 2) * i.val := rfl

/-- The ordinary real-linear real/imaginary coordinate equivalence. -/
def complexCoordinates : ℂ ≃ₗ[ℝ] (Fin 2 → ℝ) where
  toFun z := ![z.re, z.im]
  invFun v := ⟨v 0, v 1⟩
  left_inv z := Complex.eta z
  right_inv v := by
    funext c
    fin_cases c <;> rfl
  map_add' z w := by
    funext c
    fin_cases c <;> rfl
  map_smul' a z := by
    funext c
    fin_cases c <;> simp

@[simp] theorem complexCoordinates_apply (z : ℂ) : complexCoordinates z = ![z.re, z.im] := rfl

@[simp] theorem complexCoordinates_symm_apply (v : Fin 2 → ℝ) :
    complexCoordinates.symm v = (v 0 : ℂ) + (v 1 : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [complexCoordinates]

/-- Coordinates indexed transparently by `(row, column, real/imaginary)`. -/
def entryCoordinates (r s : ℕ) :
    Matrix (Fin s) (Fin r) ℂ ≃ₗ[ℝ] (CoordinateIndex r s → ℝ) where
  toFun X k := complexCoordinates (X k.1 k.2.1) k.2.2
  invFun v i j := complexCoordinates.symm (fun c => v (i, j, c))
  left_inv X := by
    funext i j
    change complexCoordinates.symm (complexCoordinates (X i j)) = X i j
    exact complexCoordinates.symm_apply_apply _
  right_inv v := by
    funext k
    rcases k with ⟨i, j, c⟩
    exact congrFun (complexCoordinates.apply_symm_apply (fun c => v (i, j, c))) c
  map_add' X Y := by
    funext k
    exact congrFun (complexCoordinates.map_add (X k.1 k.2.1) (Y k.1 k.2.1)) k.2.2
  map_smul' a X := by
    funext k
    exact congrFun (complexCoordinates.map_smul a (X k.1 k.2.1)) k.2.2

@[simp] theorem entryCoordinates_real (r s : ℕ) (X : Matrix (Fin s) (Fin r) ℂ)
    (i : Fin s) (j : Fin r) : entryCoordinates r s X (i, j, 0) = (X i j).re := rfl

@[simp] theorem entryCoordinates_imag (r s : ℕ) (X : Matrix (Fin s) (Fin r) ℂ)
    (i : Fin s) (j : Fin r) : entryCoordinates r s X (i, j, 1) = (X i j).im := rfl

@[simp] theorem entryCoordinates_symm_entry (r s : ℕ) (v : CoordinateIndex r s → ℝ)
    (i : Fin s) (j : Fin r) :
    (entryCoordinates r s).symm v i j = (v (i, j, 0) : ℂ) +
      (v (i, j, 1) : ℂ) * Complex.I := by
  change complexCoordinates.symm (fun c => v (i, j, c)) = _
  exact complexCoordinates_symm_apply _

/-- Reindex the entry coordinates and equip them with the Euclidean `L²` norm. -/
def coordinatesLinearEquiv (r s : ℕ) :
    Matrix (Fin s) (Fin r) ℂ ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (2 * r * s)) where
  toFun X := WithLp.toLp 2 (fun k => entryCoordinates r s X ((indexEquiv r s).symm k))
  invFun v := (entryCoordinates r s).symm (fun k => v (indexEquiv r s k))
  left_inv X := by
    change (entryCoordinates r s).symm
      (fun k => entryCoordinates r s X ((indexEquiv r s).symm (indexEquiv r s k))) = X
    simp only [Equiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  right_inv v := by
    apply WithLp.ofLp_injective 2
    funext k
    change entryCoordinates r s
      ((entryCoordinates r s).symm (fun k => v (indexEquiv r s k)))
        ((indexEquiv r s).symm k) = v k
    simp only [LinearEquiv.apply_symm_apply]
    change v ((indexEquiv r s) ((indexEquiv r s).symm k)) = v k
    rw [Equiv.apply_symm_apply]
  map_add' X Y := by
    apply WithLp.ofLp_injective 2
    funext k
    exact congrFun ((entryCoordinates r s).map_add X Y) ((indexEquiv r s).symm k)
  map_smul' a X := by
    apply WithLp.ofLp_injective 2
    funext k
    exact congrFun ((entryCoordinates r s).map_smul a X) ((indexEquiv r s).symm k)

theorem continuous_entryCoordinates (r s : ℕ) :
    Continuous (entryCoordinates r s : Matrix (Fin s) (Fin r) ℂ → CoordinateIndex r s → ℝ) := by
  apply continuous_pi
  intro k
  rcases k with ⟨i, j, c⟩
  fin_cases c
  · exact Complex.continuous_re.comp (continuous_apply_apply i j)
  · exact Complex.continuous_im.comp (continuous_apply_apply i j)

theorem continuous_entryCoordinates_symm (r s : ℕ) :
    Continuous ((entryCoordinates r s).symm :
      (CoordinateIndex r s → ℝ) → Matrix (Fin s) (Fin r) ℂ) := by
  apply continuous_matrix
  intro i j
  simp only [entryCoordinates_symm_entry]
  exact (Complex.continuous_ofReal.comp (continuous_apply (i, j, 0))).add
    ((Complex.continuous_ofReal.comp (continuous_apply (i, j, 1))).mul continuous_const)

/-- Actual real continuous linear equivalence, with no chosen matrix norm. -/
def coordinates (r s : ℕ) :
    Matrix (Fin s) (Fin r) ℂ ≃L[ℝ] EuclideanSpace ℝ (Fin (2 * r * s)) where
  toLinearEquiv := coordinatesLinearEquiv r s
  continuous_toFun := by
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro k
    exact (continuous_apply ((indexEquiv r s).symm k)).comp
      (continuous_entryCoordinates r s)
  continuous_invFun := by
    apply (continuous_entryCoordinates_symm r s).comp
    apply continuous_pi
    intro k
    exact PiLp.continuous_apply 2 (fun _ => ℝ) (indexEquiv r s k)

@[simp] theorem coordinates_entry (r s : ℕ) (X : Matrix (Fin s) (Fin r) ℂ)
    (k : CoordinateIndex r s) :
    coordinates r s X (indexEquiv r s k) = entryCoordinates r s X k := by
  change entryCoordinates r s X ((indexEquiv r s).symm (indexEquiv r s k)) = _
  rw [Equiv.symm_apply_apply]

@[simp] theorem coordinates_real (r s : ℕ) (X : Matrix (Fin s) (Fin r) ℂ)
    (i : Fin s) (j : Fin r) :
    coordinates r s X (indexEquiv r s (i, j, 0)) = (X i j).re := by
  rw [coordinates_entry, entryCoordinates_real]

@[simp] theorem coordinates_imag (r s : ℕ) (X : Matrix (Fin s) (Fin r) ℂ)
    (i : Fin s) (j : Fin r) :
    coordinates r s X (indexEquiv r s (i, j, 1)) = (X i j).im := by
  rw [coordinates_entry, entryCoordinates_imag]

@[simp] theorem coordinates_symm_entry (r s : ℕ)
    (v : EuclideanSpace ℝ (Fin (2 * r * s))) (i : Fin s) (j : Fin r) :
    (coordinates r s).symm v i j =
      (v (indexEquiv r s (i, j, 0)) : ℂ) +
        (v (indexEquiv r s (i, j, 1)) : ℂ) * Complex.I := by
  change complexCoordinates.symm (fun c => v (indexEquiv r s (i, j, c))) = _
  exact complexCoordinates_symm_apply _

/-- The actual Frobenius square is the sum of squared real and imaginary coordinates. -/
theorem frobeniusSq_eq_entry_sum (r s : ℕ) (X : Matrix (Fin s) (Fin r) ℂ) :
    ShellAccounting.frobeniusSq X = ∑ k, (entryCoordinates r s X k) ^ 2 := by
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, entryCoordinates_real,
    entryCoordinates_imag, ShellAccounting.frobeniusSq, Complex.sq_norm,
    Complex.normSq_apply]
  simp only [pow_two]

/-- Reindexing does not alter the real-coordinate sum of squares. -/
theorem frobeniusSq_eq_coordinate_sum (r s : ℕ) (X : Matrix (Fin s) (Fin r) ℂ) :
    ShellAccounting.frobeniusSq X = ∑ k, (coordinates r s X k) ^ 2 := by
  rw [frobeniusSq_eq_entry_sum]
  exact Fintype.sum_equiv (indexEquiv r s) _ _ (fun k => by rw [coordinates_entry])

/-- The exact Euclidean norm identity required by real graph-parameter analysis. -/
theorem frobeniusSq_eq_norm_sq (r s : ℕ) (X : Matrix (Fin s) (Fin r) ℂ) :
    ShellAccounting.frobeniusSq X = ‖coordinates r s X‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, frobeniusSq_eq_coordinate_sum]
  simp only [Real.norm_eq_abs, sq_abs]

/-- The same identity in the inverse direction. -/
theorem frobeniusSq_symm_eq_norm_sq (r s : ℕ)
    (v : EuclideanSpace ℝ (Fin (2 * r * s))) :
    ShellAccounting.frobeniusSq ((coordinates r s).symm v) = ‖v‖ ^ 2 := by
  rw [frobeniusSq_eq_norm_sq, ContinuousLinearEquiv.apply_symm_apply]

/-- Canonical measurable equivalence for Euclidean graph coordinates. -/
def measurableEquiv (r s : ℕ) :
    Matrix (Fin s) (Fin r) ℂ ≃ᵐ EuclideanSpace ℝ (Fin (2 * r * s)) :=
  (coordinates r s).toHomeomorph.toMeasurableEquiv

/-- Finite currying only regroups independent real Lebesgue coordinates.
This elementary product-measure fact is proved here from rectangles. -/
theorem volume_preserving_uncurry (α β : Type*) [Fintype α] [Fintype β] :
    MeasurePreserving (MeasurableEquiv.curry α β ℝ).symm := by
  refine ⟨(MeasurableEquiv.curry α β ℝ).symm.measurable, ?_⟩
  refine (Measure.pi_eq (fun S hS => ?_)).symm
  rw [MeasurableEquiv.map_apply]
  have hpre : (MeasurableEquiv.curry α β ℝ).symm ⁻¹' Set.pi Set.univ S =
      Set.pi Set.univ (fun i => Set.pi Set.univ (fun j => S (i, j))) := by
    ext u
    simp only [Set.mem_preimage, Set.mem_univ_pi, MeasurableEquiv.coe_curry_symm,
      Function.uncurry]
    exact ⟨fun h i j => h (i, j), fun h k => h k.1 k.2⟩
  rw [hpre, volume_pi_pi]
  simp only [volume_pi_pi, Fintype.prod_prod_type]

/-- Taking every actual complex entry to its real/imaginary pair preserves
standard product Lebesgue measure, including both finite regroupings. -/
theorem volume_preserving_entryCoordinates (r s : ℕ) :
    MeasurePreserving (entryCoordinates r s : Matrix (Fin s) (Fin r) ℂ →
      CoordinateIndex r s → ℝ) TailGeometry.matrixLebesgue volume := by
  have hcomplex : MeasurePreserving (complexCoordinates : ℂ → Fin 2 → ℝ) := by
    have heq : (complexCoordinates : ℂ → Fin 2 → ℝ) = Complex.measurableEquivPi := by
      funext z
      rfl
    rw [heq]
    exact Complex.volume_preserving_equiv_pi
  have hentries : MeasurePreserving
      (fun X : Fin s → Fin r → ℂ => fun i j => complexCoordinates (X i j)) :=
    volume_preserving_pi (fun _ : Fin s =>
      volume_preserving_pi (fun _ : Fin r => hcomplex))
  have hrows : MeasurePreserving
      (fun v : Fin s → Fin r → Fin 2 → ℝ => fun i =>
        (MeasurableEquiv.curry (Fin r) (Fin 2) ℝ).symm (v i)) :=
    volume_preserving_pi (fun _ : Fin s =>
      volume_preserving_uncurry (Fin r) (Fin 2))
  exact ((volume_preserving_uncurry (Fin s) (Fin r × Fin 2)).comp hrows).comp hentries

/-- The full explicit real Euclidean coordinates preserve the standard
complex-entry product Lebesgue measure exactly, with normalization one. -/
theorem volume_preserving_coordinates (r s : ℕ) :
    MeasurePreserving (measurableEquiv r s) TailGeometry.matrixLebesgue volume := by
  have hindex := volume_measurePreserving_piCongrLeft
    (fun _ : Fin (2 * r * s) => ℝ) (indexEquiv r s)
  have hfull := (PiLp.volume_preserving_toLp (Fin (2 * r * s))).comp
    (hindex.comp (volume_preserving_entryCoordinates r s))
  convert hfull using 1
  funext X
  apply WithLp.ofLp_injective 2
  funext k
  change entryCoordinates r s X ((indexEquiv r s).symm k) =
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (2 * r * s) => ℝ)
      (indexEquiv r s) (entryCoordinates r s X)) k
  rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  simp only [eq_rec_constant]

/-- Matrix Lebesgue measure is the pushforward of ordinary real Euclidean
volume under the actual inverse coordinate map. -/
theorem matrixLebesgue_eq_map_euclidean (r s : ℕ) :
    TailGeometry.matrixLebesgue =
      Measure.map (measurableEquiv r s).symm
        (volume : Measure (EuclideanSpace ℝ (Fin (2 * r * s)))) :=
  (volume_preserving_coordinates r s).symm.map_eq.symm

/-- The forward pushforward is Euclidean volume as well. -/
theorem map_matrixLebesgue_eq_euclidean (r s : ℕ) :
    Measure.map (measurableEquiv r s) TailGeometry.matrixLebesgue =
      (volume : Measure (EuclideanSpace ℝ (Fin (2 * r * s)))) :=
  (volume_preserving_coordinates r s).map_eq

end Paper26.MatrixCoordinates
