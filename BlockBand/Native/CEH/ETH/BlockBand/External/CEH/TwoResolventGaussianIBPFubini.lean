module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.TwoResolventGaussianIBPAggregate
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Full-product preparation for finite-coordinate GUE integration by parts

This module makes the background seen by one real GUE coordinate explicit and
proves the measurability and absolute integrability statements needed to apply
one-dimensional Gaussian integration by parts conditionally inside the full
finite product law.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.External.CEH

open Matrix MeasureTheory ProbabilityTheory
open CEHNative.BlockBand
open scoped BigOperators ComplexConjugate NNReal ComplexOrder
  Matrix.Norms.L2Operator

/-- Set one real Hermitian coordinate to zero, leaving all complementary
coordinates unchanged. -/
def eraseGUECoordinate (N : ℕ)
    (k : Fin (Fintype.card (HermitianCoordinate N)))
    (y : HermitianCoordinateSpace N) : HermitianCoordinateSpace N :=
  Function.update y k 0

/-- The Hermitian matrix reconstructed from all coordinates complementary to
`k`. -/
def complementaryGUEBackground (N : ℕ)
    (k : Fin (Fintype.card (HermitianCoordinate N)))
    (y : HermitianCoordinateSpace N) : Matrix (Fin N) (Fin N) ℂ :=
  (hermitianGUEBlock N (eraseGUECoordinate N k y)).1

/-- Complementary-coordinate reconstruction is Hermitian. -/
theorem complementaryGUEBackground_isHermitian (N : ℕ)
    (k : Fin (Fintype.card (HermitianCoordinate N)))
    (y : HermitianCoordinateSpace N) :
    (complementaryGUEBackground N k y).IsHermitian :=
  (hermitianGUEBlock N (eraseGUECoordinate N k y)).2

/-- Erasing one coordinate is Borel measurable. -/
theorem measurable_eraseGUECoordinate (N : ℕ)
    (k : Fin (Fintype.card (HermitianCoordinate N))) :
    Measurable (eraseGUECoordinate N k) := by
  rw [measurable_pi_iff]
  intro j
  by_cases hj : j = k
  · subst j
    simp [eraseGUECoordinate]
  · simpa [eraseGUECoordinate, Function.update, hj] using
      (measurable_pi_apply j : Measurable (fun y : HermitianCoordinateSpace N => y j))

/-- The complementary reconstructed matrix is Borel measurable entrywise. -/
theorem measurable_complementaryGUEBackground (N : ℕ)
    (k : Fin (Fintype.card (HermitianCoordinate N))) :
    Measurable (complementaryGUEBackground N k) := by
  apply Measurable.of_eval_matrix
  intro i j
  exact (((measurable_hermitianGUEBlock N).comp
    (measurable_eraseGUECoordinate N k)).subtype_coe.eval_matrix
      (i := i) (j := j))

private theorem finCoordinate_eq_erase_add_single
    (N : ℕ) (k : Fin (Fintype.card (HermitianCoordinate N)))
    (y : HermitianCoordinateSpace N) :
    y = eraseGUECoordinate N k y + (y k) • Pi.single k 1 := by
  funext j
  by_cases hj : j = k
  · subst j
    simp [eraseGUECoordinate]
  · simp [eraseGUECoordinate, Function.update, hj]

/-- Re-inserting the erased coordinate is exactly affine reconstruction in
its canonical Hermitian direction. -/
theorem hermitianGUEBlock_eq_complementary_add_coordinate
    (N : ℕ) (k : Fin (Fintype.card (HermitianCoordinate N)))
    (y : HermitianCoordinateSpace N) :
    (hermitianGUEBlock N y).1 =
      complementaryGUEBackground N k y +
        ((y k : ℝ) : ℂ) • gueCoordinateDirection N k := by
  have hy := finCoordinate_eq_erase_add_single N k y
  have hcomp :
      y ∘ hermitianCoordinateEquivFin N =
        (eraseGUECoordinate N k y ∘ hermitianCoordinateEquivFin N) +
          (y k) • (Pi.single k 1 ∘ hermitianCoordinateEquivFin N) := by
    funext c
    simpa using congrFun hy ((hermitianCoordinateEquivFin N) c)
  change hermitianCoordinatesLinearMap N
      (y ∘ hermitianCoordinateEquivFin N) =
    hermitianCoordinatesLinearMap N
        (eraseGUECoordinate N k y ∘ hermitianCoordinateEquivFin N) +
      (y k : ℂ) •
        hermitianCoordinatesLinearMap N
          (Pi.single k 1 ∘ hermitianCoordinateEquivFin N)
  rw [hcomp, LinearMap.map_add, LinearMap.map_smul]
  rfl

/-- Replacing coordinate `k` by a real number gives the corresponding affine
Hermitian line through the complementary background. -/
theorem hermitianGUEBlock_update_eq_coordinatePencil
    (N : ℕ) (k : Fin (Fintype.card (HermitianCoordinate N)))
    (y : HermitianCoordinateSpace N) (x : ℝ) :
    (hermitianGUEBlock N (Function.update y k x)).1 =
      complementaryGUEBackground N k y +
        (x : ℂ) • gueCoordinateDirection N k := by
  rw [hermitianGUEBlock_eq_complementary_add_coordinate N k
    (Function.update y k x)]
  congr 1
  · unfold complementaryGUEBackground eraseGUECoordinate
    congr 2
    funext j
    by_cases hj : j = k <;> simp [Function.update, hj]
  · simp [Function.update]

/-- The resolvent reconstructed from the entire GUE coordinate
field. -/
def fullGUEResolvent {N : ℕ}
    (H : Matrix (Fin N) (Fin N) ℂ) (z : ℂ)
    (y : HermitianCoordinateSpace N) : Matrix (Fin N) (Fin N) ℂ :=
  (H + (hermitianGUEBlock N y).1 -
    z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹

/-- One entry of the full-coordinate resolvent. -/
def fullGUECoordinateResolventEntry {N : ℕ}
    (H : Matrix (Fin N) (Fin N) ℂ) (z : ℂ)
    (i j : Fin N) (y : HermitianCoordinateSpace N) : ℂ :=
  fullGUEResolvent H z y i j

/-- After conditioning on the complementary coordinates, the full resolvent
is the one-dimensional affine coordinate resolvent. -/
theorem fullGUEResolvent_update_eq_coordinateResolvent {N : ℕ}
    (H : Matrix (Fin N) (Fin N) ℂ)
    (k : Fin (Fintype.card (HermitianCoordinate N)))
    (y : HermitianCoordinateSpace N) (z : ℂ) (x : ℝ) :
    fullGUEResolvent H z (Function.update y k x) =
      coordinateResolvent
        (H + complementaryGUEBackground N k y -
          z • (1 : Matrix (Fin N) (Fin N) ℂ))
        (gueCoordinateDirection N k) x := by
  unfold fullGUEResolvent coordinateResolvent coordinatePencil
  rw [hermitianGUEBlock_update_eq_coordinatePencil]
  congr 1
  abel

/-- Every full-coordinate resolvent entry is Borel measurable. -/
theorem measurable_fullGUECoordinateResolventEntry {N : ℕ}
    (H : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (i j : Fin N) :
    Measurable (fullGUECoordinateResolventEntry H z i j) := by
  let A : HermitianCoordinateSpace N → Matrix (Fin N) (Fin N) ℂ :=
    fun y => H + (hermitianGUEBlock N y).1 -
      z • (1 : Matrix (Fin N) (Fin N) ℂ)
  have hA (p q : Fin N) : Measurable (fun y => A y p q) := by
    exact (measurable_const.add
      ((measurable_hermitianGUEBlock N).subtype_coe.eval_matrix
        (i := p) (j := q))).sub measurable_const
  have detMeas (B : HermitianCoordinateSpace N →
      Matrix (Fin N) (Fin N) ℂ)
      (hB : ∀ p q, Measurable (fun y => B y p q)) :
      Measurable (fun y => (B y).det) := by
    simp only [Matrix.det_apply']
    fun_prop
  have hdet : Measurable (fun y => (A y).det) := detMeas A hA
  unfold fullGUECoordinateResolventEntry fullGUEResolvent
  change Measurable (fun y => (A y)⁻¹ i j)
  simp only [Matrix.inv_def, Ring.inverse_eq_inv]
  apply hdet.inv.mul
  apply detMeas
  intro p q
  simp only [Matrix.updateCol_apply, Matrix.transpose_apply]
  split_ifs
  · exact measurable_const
  · exact hA q p

/-- Uniform nonreal resolvent bound on the full GUE coordinate space. -/
theorem norm_fullGUECoordinateResolventEntry_le {N : ℕ}
    (H : Matrix (Fin N) (Fin N) ℂ) (hH : H.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) (i j : Fin N)
    (y : HermitianCoordinateSpace N) :
    ‖fullGUECoordinateResolventEntry H z i j y‖ ≤ |z.im|⁻¹ := by
  have hHW : (H + (hermitianGUEBlock N y).1).IsHermitian :=
    hH.add (hermitianGUEBlock N y).2
  simpa [fullGUECoordinateResolventEntry, fullGUEResolvent,
    coordinateResolvent, coordinatePencil] using
    (norm_coordinateHermitianResolvent_entry_le
      (H + (hermitianGUEBlock N y).1) 0 hHW Matrix.isHermitian_zero
      hz i j 0)

/-- A full-coordinate resolvent entry is absolutely integrable under the
normalized GUE product law. -/
theorem integrable_fullGUECoordinateResolventEntry {N : ℕ}
    (H : Matrix (Fin N) (Fin N) ℂ) (hH : H.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) (i j : Fin N) :
    Integrable (fullGUECoordinateResolventEntry H z i j)
      (hermitianGUECoordinateMeasure N (1 / (N : ℝ)) (by positivity)) := by
  apply Integrable.of_bound
    (measurable_fullGUECoordinateResolventEntry H z i j).aestronglyMeasurable
    |z.im|⁻¹
  exact ae_of_all _ (norm_fullGUECoordinateResolventEntry_le H hH hz i j)

/-- The derivative observable produced by differentiating the full resolvent
in one GUE coordinate. -/
def fullGUECoordinateDerivativeEntry {N : ℕ}
    (H : Matrix (Fin N) (Fin N) ℂ) (z : ℂ)
    (k : Fin (Fintype.card (HermitianCoordinate N)))
    (i j : Fin N) (y : HermitianCoordinateSpace N) : ℂ :=
  -(fullGUEResolvent H z y * gueCoordinateDirection N k *
    fullGUEResolvent H z y) i j

/-- The full-coordinate derivative observable is Borel measurable. -/
theorem measurable_fullGUECoordinateDerivativeEntry {N : ℕ}
    (H : Matrix (Fin N) (Fin N) ℂ) (z : ℂ)
    (k : Fin (Fintype.card (HermitianCoordinate N))) (i j : Fin N) :
    Measurable (fullGUECoordinateDerivativeEntry H z k i j) := by
  unfold fullGUECoordinateDerivativeEntry
  simp only [Matrix.mul_apply]
  apply Measurable.neg
  apply Finset.measurable_sum
  intro b hb
  apply Measurable.mul
  · apply Finset.measurable_sum
    intro a ha
    exact (measurable_fullGUECoordinateResolventEntry H z i a).mul
      measurable_const
  · exact measurable_fullGUECoordinateResolventEntry H z b j

/-- Uniform bound for the full-coordinate derivative observable. -/
theorem norm_fullGUECoordinateDerivativeEntry_le {N : ℕ}
    (H : Matrix (Fin N) (Fin N) ℂ) (hH : H.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0)
    (k : Fin (Fintype.card (HermitianCoordinate N)))
    (i j : Fin N) (y : HermitianCoordinateSpace N) :
    ‖fullGUECoordinateDerivativeEntry H z k i j y‖ ≤
      |z.im|⁻¹ ^ 2 *
        ∑ a : Fin N, ∑ b : Fin N, ‖gueCoordinateDirection N k a b‖ := by
  have hHW : (H + (hermitianGUEBlock N y).1).IsHermitian :=
    hH.add (hermitianGUEBlock N y).2
  rw [fullGUECoordinateDerivativeEntry, norm_neg]
  simpa [fullGUEResolvent, coordinateResolvent, coordinatePencil] using
    (norm_coordinateHermitianResolvent_derivative_le
      (H + (hermitianGUEBlock N y).1) (gueCoordinateDirection N k)
      hHW (gueCoordinateDirection_isHermitian N k) hz i j 0)

/-- The derivative observable is absolutely integrable on the entire
normalized GUE coordinate product. -/
theorem integrable_fullGUECoordinateDerivativeEntry {N : ℕ}
    (H : Matrix (Fin N) (Fin N) ℂ) (hH : H.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0)
    (k : Fin (Fintype.card (HermitianCoordinate N)))
    (i j : Fin N) :
    Integrable (fullGUECoordinateDerivativeEntry H z k i j)
      (hermitianGUECoordinateMeasure N (1 / (N : ℝ)) (by positivity)) := by
  apply Integrable.of_bound
    (measurable_fullGUECoordinateDerivativeEntry H z k i j).aestronglyMeasurable
    (|z.im|⁻¹ ^ 2 *
      ∑ a : Fin N, ∑ b : Fin N, ‖gueCoordinateDirection N k a b‖)
  exact ae_of_all _
    (norm_fullGUECoordinateDerivativeEntry_le H hH hz k i j)

/-- Every real GUE coordinate has a finite first moment under the full
normalized product law. -/
theorem integrable_normalizedGUECoordinate {N : ℕ}
    (k : Fin (Fintype.card (HermitianCoordinate N))) :
    Integrable (fun y : HermitianCoordinateSpace N => y k)
      (hermitianGUECoordinateMeasure N (1 / (N : ℝ)) (by positivity)) := by
  unfold hermitianGUECoordinateMeasure
  apply integrable_eval
  exact ProbabilityTheory.IsGaussian.integrable_id

/-- The coordinate times its background-dependent full resolvent entry is
absolutely integrable; this is the global version of the first density
premise in scalar Gaussian IBP. -/
theorem integrable_coordinate_mul_fullGUEResolventEntry {N : ℕ}
    (H : Matrix (Fin N) (Fin N) ℂ) (hH : H.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0)
    (k : Fin (Fintype.card (HermitianCoordinate N)))
    (i j : Fin N) :
    Integrable (fun y : HermitianCoordinateSpace N =>
      (y k : ℂ) * fullGUECoordinateResolventEntry H z i j y)
      (hermitianGUECoordinateMeasure N (1 / (N : ℝ)) (by positivity)) := by
  have hkC : Integrable
      (fun y : HermitianCoordinateSpace N => ((y k : ℝ) : ℂ))
      (hermitianGUECoordinateMeasure N (1 / (N : ℝ)) (by positivity)) :=
    (integrable_normalizedGUECoordinate k).ofReal
  exact hkC.mul_bdd
    (measurable_fullGUECoordinateResolventEntry H z i j).aestronglyMeasurable
    (ae_of_all _ (norm_fullGUECoordinateResolventEntry_le H hH hz i j))

/-- **Conditional coordinate IBP for the full GUE resolvent.**
All complementary coordinates are held fixed, but the displayed observable is
the full reconstructed resolvent after replacing coordinate `k`. -/
theorem normalizedGUEFullResolvent_conditionalCoordinate_IBP
    {N : ℕ} (hN : 0 < N)
    (H : Matrix (Fin N) (Fin N) ℂ) (hH : H.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0)
    (k : Fin (Fintype.card (HermitianCoordinate N)))
    (i j : Fin N) (y : HermitianCoordinateSpace N) :
    (∫ x : ℝ, (x : ℂ) *
        fullGUECoordinateResolventEntry H z i j
          (Function.update y k x)
      ∂gaussianReal 0
        (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
          (by positivity) k)) =
      (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
        (by positivity) k : ℝ) *
        ∫ x : ℝ,
          fullGUECoordinateDerivativeEntry H z k i j
            (Function.update y k x)
        ∂gaussianReal 0
          (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
            (by positivity) k) := by
  let H₀ := H + complementaryGUEBackground N k y
  have hH₀ : H₀.IsHermitian :=
    hH.add (complementaryGUEBackground_isHermitian N k y)
  have hibp := normalizedGUECoordinateHermitianResolventEntry_IBP
    hN H₀ hH₀ hz k i j
  have hentry (x : ℝ) :
      fullGUECoordinateResolventEntry H z i j (Function.update y k x) =
        coordinateResolvent
          (H₀ - z • (1 : Matrix (Fin N) (Fin N) ℂ))
          (gueCoordinateDirection N k) x i j := by
    change fullGUEResolvent H z (Function.update y k x) i j = _
    rw [fullGUEResolvent_update_eq_coordinateResolvent]
  have hderiv (x : ℝ) :
      fullGUECoordinateDerivativeEntry H z k i j
          (Function.update y k x) =
        -(coordinateResolvent
            (H₀ - z • (1 : Matrix (Fin N) (Fin N) ℂ))
            (gueCoordinateDirection N k) x *
          gueCoordinateDirection N k *
          coordinateResolvent
            (H₀ - z • (1 : Matrix (Fin N) (Fin N) ℂ))
            (gueCoordinateDirection N k) x) i j := by
    unfold fullGUECoordinateDerivativeEntry
    rw [fullGUEResolvent_update_eq_coordinateResolvent]
  calc
    _ = ∫ x : ℝ, (x : ℂ) *
          coordinateResolvent
            (H₀ - z • (1 : Matrix (Fin N) (Fin N) ℂ))
            (gueCoordinateDirection N k) x i j
        ∂gaussianReal 0
          (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
            (by positivity) k) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [hentry]
    _ = _ := hibp
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards with x
      exact (hderiv x).symm

/-- A background-dependent two-resolvent entry under one common full
GUE matrix. -/
def fullGUEPlainTwoResolventEntry {N : ℕ}
    (H₁ H₂ A : Matrix (Fin N) (Fin N) ℂ) (z₁ z₂ : ℂ)
    (i j : Fin N) (y : HermitianCoordinateSpace N) : ℂ :=
  (fullGUEResolvent H₁ z₁ y * A * fullGUEResolvent H₂ z₂ y) i j

/-- Joint measurability of the two-resolvent entry in all normalized
GUE coordinates. -/
theorem measurable_fullGUEPlainTwoResolventEntry {N : ℕ}
    (H₁ H₂ A : Matrix (Fin N) (Fin N) ℂ) (z₁ z₂ : ℂ)
    (i j : Fin N) :
    Measurable (fullGUEPlainTwoResolventEntry H₁ H₂ A z₁ z₂ i j) := by
  unfold fullGUEPlainTwoResolventEntry
  simp only [Matrix.mul_apply]
  apply Finset.measurable_sum
  intro b hb
  apply Measurable.mul
  · apply Finset.measurable_sum
    intro a ha
    exact (measurable_fullGUECoordinateResolventEntry H₁ z₁ i a).mul
      measurable_const
  · exact measurable_fullGUECoordinateResolventEntry H₂ z₂ b j

/-- A uniform entrywise bound for a two-resolvent word. -/
theorem norm_fullGUEPlainTwoResolventEntry_le {N : ℕ}
    (H₁ H₂ A : Matrix (Fin N) (Fin N) ℂ)
    (hH₁ : H₁.IsHermitian) (hH₂ : H₂.IsHermitian)
    {z₁ z₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (i j : Fin N) (y : HermitianCoordinateSpace N) :
    ‖fullGUEPlainTwoResolventEntry H₁ H₂ A z₁ z₂ i j y‖ ≤
      |z₁.im|⁻¹ * |z₂.im|⁻¹ *
        ∑ a : Fin N, ∑ b : Fin N, ‖A a b‖ := by
  unfold fullGUEPlainTwoResolventEntry
  simp only [Matrix.mul_apply]
  calc
    ‖∑ b, (∑ a, fullGUEResolvent H₁ z₁ y i a * A a b) *
          fullGUEResolvent H₂ z₂ y b j‖
        ≤ ∑ b, ‖(∑ a, fullGUEResolvent H₁ z₁ y i a * A a b) *
          fullGUEResolvent H₂ z₂ y b j‖ := norm_sum_le _ _
    _ ≤ ∑ b, ∑ a, |z₁.im|⁻¹ * |z₂.im|⁻¹ * ‖A a b‖ := by
      apply Finset.sum_le_sum
      intro b hb
      calc
        _ ≤ ‖∑ a, fullGUEResolvent H₁ z₁ y i a * A a b‖ *
              ‖fullGUEResolvent H₂ z₂ y b j‖ := norm_mul_le _ _
        _ ≤ (∑ a, ‖fullGUEResolvent H₁ z₁ y i a * A a b‖) *
              ‖fullGUEResolvent H₂ z₂ y b j‖ := by
          gcongr
          exact norm_sum_le _ _
        _ ≤ (∑ a, |z₁.im|⁻¹ * ‖A a b‖) * |z₂.im|⁻¹ := by
          gcongr
          · exact (norm_mul_le _ _).trans
              (mul_le_mul_of_nonneg_right
                (norm_fullGUECoordinateResolventEntry_le
                  H₁ hH₁ hz₁ i a y) (norm_nonneg _))
          · exact norm_fullGUECoordinateResolventEntry_le
              H₂ hH₂ hz₂ b j y
        _ = ∑ a, |z₁.im|⁻¹ * |z₂.im|⁻¹ * ‖A a b‖ := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro a ha
          ring
    _ = |z₁.im|⁻¹ * |z₂.im|⁻¹ *
          ∑ a, ∑ b, ‖A a b‖ := by
      rw [Finset.mul_sum, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]

/-- Absolute integrability of the two-resolvent entry under the full
normalized GUE coordinate law. -/
theorem integrable_fullGUEPlainTwoResolventEntry {N : ℕ}
    (H₁ H₂ A : Matrix (Fin N) (Fin N) ℂ)
    (hH₁ : H₁.IsHermitian) (hH₂ : H₂.IsHermitian)
    {z₁ z₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (i j : Fin N) :
    Integrable (fullGUEPlainTwoResolventEntry H₁ H₂ A z₁ z₂ i j)
      (hermitianGUECoordinateMeasure N (1 / (N : ℝ)) (by positivity)) := by
  apply Integrable.of_bound
    (measurable_fullGUEPlainTwoResolventEntry
      H₁ H₂ A z₁ z₂ i j).aestronglyMeasurable
    (|z₁.im|⁻¹ * |z₂.im|⁻¹ *
      ∑ a : Fin N, ∑ b : Fin N, ‖A a b‖)
  exact ae_of_all _
    (norm_fullGUEPlainTwoResolventEntry_le
      H₁ H₂ A hH₁ hH₂ hz₁ hz₂ i j)

/-- The coordinate-weighted two-resolvent word is absolutely
integrable, the Tonelli input for conditional Gaussian IBP. -/
theorem integrable_coordinate_mul_fullGUEPlainTwoResolventEntry {N : ℕ}
    (H₁ H₂ A : Matrix (Fin N) (Fin N) ℂ)
    (hH₁ : H₁.IsHermitian) (hH₂ : H₂.IsHermitian)
    {z₁ z₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (k : Fin (Fintype.card (HermitianCoordinate N)))
    (i j : Fin N) :
    Integrable (fun y : HermitianCoordinateSpace N =>
      (y k : ℂ) *
        fullGUEPlainTwoResolventEntry H₁ H₂ A z₁ z₂ i j y)
      (hermitianGUECoordinateMeasure N (1 / (N : ℝ)) (by positivity)) := by
  have hkC : Integrable
      (fun y : HermitianCoordinateSpace N => ((y k : ℝ) : ℂ))
      (hermitianGUECoordinateMeasure N (1 / (N : ℝ)) (by positivity)) :=
    (integrable_normalizedGUECoordinate k).ofReal
  exact hkC.mul_bdd
    (measurable_fullGUEPlainTwoResolventEntry
      H₁ H₂ A z₁ z₂ i j).aestronglyMeasurable
    (ae_of_all _ (norm_fullGUEPlainTwoResolventEntry_le
      H₁ H₂ A hH₁ hH₂ hz₁ hz₂ i j))

/-- The product-rule derivative of the two-resolvent word in one
real GUE coordinate. -/
def fullGUEPlainTwoResolventDerivativeEntry {N : ℕ}
    (H₁ H₂ A : Matrix (Fin N) (Fin N) ℂ) (z₁ z₂ : ℂ)
    (k : Fin (Fintype.card (HermitianCoordinate N)))
    (i j : Fin N) (y : HermitianCoordinateSpace N) : ℂ :=
  ((-(fullGUEResolvent H₁ z₁ y * gueCoordinateDirection N k *
        fullGUEResolvent H₁ z₁ y)) *
      A * fullGUEResolvent H₂ z₂ y +
    fullGUEResolvent H₁ z₁ y * A *
      (-(fullGUEResolvent H₂ z₂ y * gueCoordinateDirection N k *
        fullGUEResolvent H₂ z₂ y))) i j

/-- Joint measurability of the product-rule derivative in all coordinates. -/
theorem measurable_fullGUEPlainTwoResolventDerivativeEntry {N : ℕ}
    (H₁ H₂ A : Matrix (Fin N) (Fin N) ℂ) (z₁ z₂ : ℂ)
    (k : Fin (Fintype.card (HermitianCoordinate N)))
    (i j : Fin N) :
    Measurable
      (fullGUEPlainTwoResolventDerivativeEntry H₁ H₂ A z₁ z₂ k i j) := by
  unfold fullGUEPlainTwoResolventDerivativeEntry
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.neg_apply]
  apply Measurable.add
  · apply Finset.measurable_sum
    intro b hb
    apply Measurable.mul
    · apply Finset.measurable_sum
      intro a ha
      exact (measurable_fullGUECoordinateDerivativeEntry
        H₁ z₁ k i a).mul measurable_const
    · exact measurable_fullGUECoordinateResolventEntry H₂ z₂ b j
  · apply Finset.measurable_sum
    intro b hb
    apply Measurable.mul
    · apply Finset.measurable_sum
      intro a ha
      exact (measurable_fullGUECoordinateResolventEntry H₁ z₁ i a).mul
        measurable_const
    · exact measurable_fullGUECoordinateDerivativeEntry H₂ z₂ k b j

private theorem norm_matrixTriple_entry_le
    {N : ℕ} (X A Z : Matrix (Fin N) (Fin N) ℂ)
    {cX cZ : ℝ} (hcX : 0 ≤ cX) (_hcZ : 0 ≤ cZ)
    (hX : ∀ p q, ‖X p q‖ ≤ cX) (hZ : ∀ p q, ‖Z p q‖ ≤ cZ)
    (i j : Fin N) :
    ‖(X * A * Z) i j‖ ≤
      cX * cZ * ∑ a : Fin N, ∑ b : Fin N, ‖A a b‖ := by
  simp only [Matrix.mul_apply]
  calc
    _ ≤ ∑ b, ‖(∑ a, X i a * A a b) * Z b j‖ := norm_sum_le _ _
    _ ≤ ∑ b, ∑ a, cX * cZ * ‖A a b‖ := by
      apply Finset.sum_le_sum
      intro b hb
      calc
        _ ≤ ‖∑ a, X i a * A a b‖ * ‖Z b j‖ := norm_mul_le _ _
        _ ≤ (∑ a, ‖X i a * A a b‖) * ‖Z b j‖ := by
          gcongr
          exact norm_sum_le _ _
        _ ≤ (∑ a, cX * ‖A a b‖) * cZ := by
          gcongr
          · exact (norm_mul_le _ _).trans
              (mul_le_mul_of_nonneg_right (hX i a) (norm_nonneg _))
          · exact hZ b j
        _ = ∑ a, cX * cZ * ‖A a b‖ := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro a ha
          ring
    _ = cX * cZ * ∑ a, ∑ b, ‖A a b‖ := by
      rw [Finset.mul_sum, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]

/-- A uniform bound for the product-rule derivative. -/
theorem norm_fullGUEPlainTwoResolventDerivativeEntry_le {N : ℕ}
    (H₁ H₂ A : Matrix (Fin N) (Fin N) ℂ)
    (hH₁ : H₁.IsHermitian) (hH₂ : H₂.IsHermitian)
    {z₁ z₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (k : Fin (Fintype.card (HermitianCoordinate N)))
    (i j : Fin N) (y : HermitianCoordinateSpace N) :
    ‖fullGUEPlainTwoResolventDerivativeEntry
        H₁ H₂ A z₁ z₂ k i j y‖ ≤
      (|z₁.im|⁻¹ ^ 2 *
          ∑ a : Fin N, ∑ b : Fin N, ‖gueCoordinateDirection N k a b‖) *
          |z₂.im|⁻¹ * (∑ a : Fin N, ∑ b : Fin N, ‖A a b‖) +
      |z₁.im|⁻¹ *
        (|z₂.im|⁻¹ ^ 2 *
          ∑ a : Fin N, ∑ b : Fin N, ‖gueCoordinateDirection N k a b‖) *
          (∑ a : Fin N, ∑ b : Fin N, ‖A a b‖) := by
  let E₁ := -(fullGUEResolvent H₁ z₁ y * gueCoordinateDirection N k *
    fullGUEResolvent H₁ z₁ y)
  let E₂ := -(fullGUEResolvent H₂ z₂ y * gueCoordinateDirection N k *
    fullGUEResolvent H₂ z₂ y)
  have hE₁ (p q : Fin N) :
      ‖E₁ p q‖ ≤ |z₁.im|⁻¹ ^ 2 *
        ∑ a : Fin N, ∑ b : Fin N, ‖gueCoordinateDirection N k a b‖ := by
    exact norm_fullGUECoordinateDerivativeEntry_le H₁ hH₁ hz₁ k p q y
  have hE₂ (p q : Fin N) :
      ‖E₂ p q‖ ≤ |z₂.im|⁻¹ ^ 2 *
        ∑ a : Fin N, ∑ b : Fin N, ‖gueCoordinateDirection N k a b‖ := by
    exact norm_fullGUECoordinateDerivativeEntry_le H₂ hH₂ hz₂ k p q y
  unfold fullGUEPlainTwoResolventDerivativeEntry
  change ‖(E₁ * A * fullGUEResolvent H₂ z₂ y +
    fullGUEResolvent H₁ z₁ y * A * E₂) i j‖ ≤ _
  exact (norm_add_le _ _).trans (add_le_add
    (norm_matrixTriple_entry_le E₁ A (fullGUEResolvent H₂ z₂ y)
      (by positivity) (by positivity) hE₁
      (fun p q => norm_fullGUECoordinateResolventEntry_le
        H₂ hH₂ hz₂ p q y) i j)
    (norm_matrixTriple_entry_le (fullGUEResolvent H₁ z₁ y) A E₂
      (by positivity) (by positivity)
      (fun p q => norm_fullGUECoordinateResolventEntry_le
        H₁ hH₁ hz₁ p q y) hE₂ i j))

/-- Absolute integrability of the product-rule derivative, the remaining
Tonelli input before the coordinatewise identities are summed. -/
theorem integrable_fullGUEPlainTwoResolventDerivativeEntry {N : ℕ}
    (H₁ H₂ A : Matrix (Fin N) (Fin N) ℂ)
    (hH₁ : H₁.IsHermitian) (hH₂ : H₂.IsHermitian)
    {z₁ z₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (k : Fin (Fintype.card (HermitianCoordinate N)))
    (i j : Fin N) :
    Integrable
      (fullGUEPlainTwoResolventDerivativeEntry H₁ H₂ A z₁ z₂ k i j)
      (hermitianGUECoordinateMeasure N (1 / (N : ℝ)) (by positivity)) := by
  apply Integrable.of_bound
    (measurable_fullGUEPlainTwoResolventDerivativeEntry
      H₁ H₂ A z₁ z₂ k i j).aestronglyMeasurable
    ((|z₁.im|⁻¹ ^ 2 *
        ∑ a : Fin N, ∑ b : Fin N, ‖gueCoordinateDirection N k a b‖) *
        |z₂.im|⁻¹ * (∑ a : Fin N, ∑ b : Fin N, ‖A a b‖) +
      |z₁.im|⁻¹ *
        (|z₂.im|⁻¹ ^ 2 *
          ∑ a : Fin N, ∑ b : Fin N, ‖gueCoordinateDirection N k a b‖) *
          (∑ a : Fin N, ∑ b : Fin N, ‖A a b‖))
  exact ae_of_all _ (norm_fullGUEPlainTwoResolventDerivativeEntry_le
    H₁ H₂ A hH₁ hH₂ hz₁ hz₂ k i j)

end CEHNative.BlockBand.External.CEH
