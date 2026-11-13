module

public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.SharpResolventWeightedDysonIBP

/-!
# Product domination for resolvent-weighted Dyson tests

This module establishes the analytic product-space layer for the
resolvent-weighted coordinate tests.  Every measurability and integrability
claim is proved from the explicit inverse bounds and Hermitian support of the
background marginal; none is assumed.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace ERNative.BlockBand
namespace GaussianRing
namespace ERSharpCoordinateIBP

open Matrix MeasureTheory ProbabilityTheory
open ERGaussianCoordinate ERResolventMomentIBP ERProfile
open ERComplementBackgroundReconstruction ERConcrete
open scoped BigOperators NNReal Matrix.Norms.L2Operator

local instance (p : Params) : NeZero p.n := p.nNeZero

/-- Exact norm of the lower even-moment factor. -/
theorem norm_lowerConjugateMomentTest (m : ℕ) (w : ℂ) :
    ‖lowerConjugateMomentTest m w‖ = ‖w‖ ^ (2 * m) := by
  simp [lowerConjugateMomentTest, norm_pow]
  ring_nf

/-- A uniform bound for the derivative of the lower even-moment factor.  The
`max 1 C` avoids a spurious lower bound on the fluctuation scale. -/
theorem norm_lowerConjugateMomentDerivative_le
    (m : ℕ) (w dw : ℂ) {C D : ℝ}
    (hD : 0 ≤ D) (hw : ‖w‖ ≤ C) (hdw : ‖dw‖ ≤ D) :
    ‖lowerConjugateMomentDerivative m w dw‖ ≤
      (2 * m : ℝ) * (max 1 C) ^ (m - 1) * D * (max 1 C) ^ m := by
  have hR : ‖w‖ ≤ max 1 C := hw.trans (le_max_right _ _)
  rw [lowerConjugateMomentDerivative]
  calc
    _ ≤ ‖((m : ℕ) : ℂ) * w ^ (m - 1) * dw *
          (starRingEnd ℂ w) ^ m‖ +
        ‖((m : ℕ) : ℂ) * w ^ m *
          (starRingEnd ℂ w) ^ (m - 1) * starRingEnd ℂ dw‖ := norm_add_le _ _
    _ = (m : ℝ) * ‖w‖ ^ (m - 1) * ‖dw‖ * ‖w‖ ^ m +
        (m : ℝ) * ‖w‖ ^ m * ‖w‖ ^ (m - 1) * ‖dw‖ := by
      simp only [norm_mul, norm_pow, Complex.norm_natCast]
      rw [show ‖starRingEnd ℂ w‖ = ‖w‖ by exact norm_star _,
        show ‖starRingEnd ℂ dw‖ = ‖dw‖ by exact norm_star _]
    _ ≤ (m : ℝ) * (max 1 C) ^ (m - 1) * D * (max 1 C) ^ m +
        (m : ℝ) * (max 1 C) ^ m * (max 1 C) ^ (m - 1) * D := by
      gcongr
    _ = _ := by
      ring

/-- Joint measurability of the lower even-moment factor. -/
theorem measurable_lowerConjugateMomentTest
    (m : ℕ) {α : Type*} [MeasurableSpace α] {F : α → ℂ}
    (hF : Measurable F) :
    Measurable (fun v => lowerConjugateMomentTest m (F v)) := by
  unfold lowerConjugateMomentTest
  exact (hF.pow_const _).mul
    ((Complex.continuous_conj.measurable.comp hF).pow_const _)

/-- Joint measurability of the displayed lower-moment derivative. -/
theorem measurable_lowerConjugateMomentDerivative
    (m : ℕ) {α : Type*} [MeasurableSpace α] {F dF : α → ℂ}
    (hF : Measurable F) (hdF : Measurable dF) :
    Measurable (fun v => lowerConjugateMomentDerivative m (F v) (dF v)) := by
  unfold lowerConjugateMomentDerivative
  fun_prop

/-- The resolvent-weighted test is jointly measurable in both Gaussian
coordinates and the background matrix. -/
theorem measurable_coordinateResolventLowerTest_product
    (p : Params) (a b x y i j : Site p.n p.W) (z : ℂ) (m : ℕ) :
    Measurable (fun v : (ℝ × ℝ) ×
      Matrix (Site p.n p.W) (Site p.n p.W) ℂ =>
        coordinateResolventLowerTest p v.2 a b x y i j z m v.1.1 v.1.2) := by
  unfold coordinateResolventLowerTest
  exact (measurable_sourceInverse_productEntry p a b i j z).mul
    (measurable_lowerConjugateMomentTest m
      (measurable_coordinateSignedError_product p a b x y z))

/-- The real derivative test is jointly measurable. -/
theorem measurable_coordinateResolventLowerDerivReal_product
    (p : Params) (a b x y i j : Site p.n p.W) (z : ℂ) (m : ℕ) :
    Measurable (fun v : (ℝ × ℝ) ×
      Matrix (Site p.n p.W) (Site p.n p.W) ℂ =>
        coordinateResolventLowerDerivReal p v.2 a b x y i j z m
          v.1.1 v.1.2) := by
  unfold coordinateResolventLowerDerivReal
  have hia := measurable_sourceInverse_productEntry p a b i a z
  have hbj := measurable_sourceInverse_productEntry p a b b j z
  have hib := measurable_sourceInverse_productEntry p a b i b z
  have haj := measurable_sourceInverse_productEntry p a b a j z
  have hij := measurable_sourceInverse_productEntry p a b i j z
  have hw := measurable_coordinateSignedError_product p a b x y z
  have hdw := measurable_coordinateSignedErrorDerivReal_product p a b x y z
  exact ((hia.mul hbj).add (hib.mul haj)).neg.mul
      (measurable_lowerConjugateMomentTest m hw) |>.add
    (hij.mul (measurable_lowerConjugateMomentDerivative m hw hdw))

/-- The imaginary derivative test is jointly measurable. -/
theorem measurable_coordinateResolventLowerDerivImaginary_product
    (p : Params) (a b x y i j : Site p.n p.W) (z : ℂ) (m : ℕ) :
    Measurable (fun v : (ℝ × ℝ) ×
      Matrix (Site p.n p.W) (Site p.n p.W) ℂ =>
        coordinateResolventLowerDerivImaginary p v.2 a b x y i j z m
          v.1.1 v.1.2) := by
  unfold coordinateResolventLowerDerivImaginary
  have hia := measurable_sourceInverse_productEntry p a b i a z
  have hbj := measurable_sourceInverse_productEntry p a b b j z
  have hib := measurable_sourceInverse_productEntry p a b i b z
  have haj := measurable_sourceInverse_productEntry p a b a j z
  have hij := measurable_sourceInverse_productEntry p a b i j z
  have hw := measurable_coordinateSignedError_product p a b x y z
  have hdw :=
    measurable_coordinateSignedErrorDerivImaginary_product p a b x y z
  exact ((measurable_const.mul hia |>.mul hbj).add
      (measurable_const.mul hib |>.mul haj)).mul
      (measurable_lowerConjugateMomentTest m hw) |>.add
    (hij.mul (measurable_lowerConjugateMomentDerivative m hw hdw))

/-- Uniform domination of the resolvent-weighted lower-moment test. -/
theorem Law.ae_norm_coordinateResolventLowerTest_le
    {p : Params} (M : Law p) (q₀ : UpperPair p)
    (hne : q₀.1.1 ≠ q₀.1.2) (x y i j : Site p.n p.W)
    (z : ℂ) (hz : 0 < z.im) (m : ℕ) :
    ∀ᵐ v ∂strictCoordinateProductMeasure M q₀,
      ‖coordinateResolventLowerTest p v.2 q₀.1.1 q₀.1.2
          x y i j z m v.1.1 v.1.2‖ ≤
        (z.im)⁻¹ *
          ((z.im)⁻¹ + ‖erSemicircleStieltjes z‖) ^ (2 * m) := by
  filter_upwards [Law.strictCoordinateProduct_ae_isHermitian M q₀ hne] with v hB
  rw [coordinateResolventLowerTest, norm_mul,
    norm_lowerConjugateMomentTest]
  exact mul_le_mul
    (norm_sourceInverse_coordinate_le v.2 hB q₀.1.1 q₀.1.2
      i j z hz v.1.1 v.1.2)
    (pow_le_pow_left₀ (norm_nonneg _)
      (norm_coordinateSignedError_le p v.2 hB q₀.1.1 q₀.1.2
        x y z hz v.1.1 v.1.2) _)
    (by positivity) (inv_nonneg.mpr hz.le)

/-- Explicit uniform bound used for either coordinate derivative of the
resolvent-weighted test. -/
def resolventWeightedDerivativeBound (z : ℂ) (m : ℕ) : ℝ :=
  let E := (z.im)⁻¹
  let C := E + ‖erSemicircleStieltjes z‖
  let R := max 1 C
  2 * E ^ 2 * R ^ (2 * m) +
    E * ((2 * m : ℝ) * R ^ (m - 1) * (2 * E ^ 2) * R ^ m)

/-- The full real derivative test is uniformly dominated on the strict
coordinate/background product. -/
theorem Law.ae_norm_coordinateResolventLowerDerivReal_le
    {p : Params} (M : Law p) (q₀ : UpperPair p)
    (hne : q₀.1.1 ≠ q₀.1.2) (x y i j : Site p.n p.W)
    (z : ℂ) (hz : 0 < z.im) (m : ℕ) :
    ∀ᵐ v ∂strictCoordinateProductMeasure M q₀,
      ‖coordinateResolventLowerDerivReal p v.2 q₀.1.1 q₀.1.2
          x y i j z m v.1.1 v.1.2‖ ≤
        resolventWeightedDerivativeBound z m := by
  filter_upwards [Law.strictCoordinateProduct_ae_isHermitian M q₀ hne] with v hB
  let E := (z.im)⁻¹
  let C := E + ‖erSemicircleStieltjes z‖
  let R := max 1 C
  let D := 2 * E ^ 2
  have hE : 0 ≤ E := inv_nonneg.mpr hz.le
  have hG (u w : Site p.n p.W) :
      ‖sourceInverse (coordinateMatrix v.2 q₀.1.1 q₀.1.2
        v.1.1 v.1.2) z u w‖ ≤ E :=
    norm_sourceInverse_coordinate_le v.2 hB q₀.1.1 q₀.1.2
      u w z hz v.1.1 v.1.2
  have hw : ‖coordinateSignedError p v.2 q₀.1.1 q₀.1.2
      x y z v.1.1 v.1.2‖ ≤ C :=
    norm_coordinateSignedError_le p v.2 hB q₀.1.1 q₀.1.2
      x y z hz v.1.1 v.1.2
  have hdw : ‖coordinateSignedErrorDerivReal p v.2 q₀.1.1 q₀.1.2
      x y z v.1.1 v.1.2‖ ≤ D :=
    norm_coordinateSignedErrorDerivReal_le p v.2 hB q₀.1.1 q₀.1.2
      x y z hz v.1.1 v.1.2
  have hL : ‖lowerConjugateMomentTest m
      (coordinateSignedError p v.2 q₀.1.1 q₀.1.2
        x y z v.1.1 v.1.2)‖ ≤ R ^ (2 * m) := by
    rw [norm_lowerConjugateMomentTest]
    exact pow_le_pow_left₀ (norm_nonneg _) (hw.trans (le_max_right _ _)) _
  have hdL : ‖lowerConjugateMomentDerivative m
      (coordinateSignedError p v.2 q₀.1.1 q₀.1.2
        x y z v.1.1 v.1.2)
      (coordinateSignedErrorDerivReal p v.2 q₀.1.1 q₀.1.2
        x y z v.1.1 v.1.2)‖ ≤
      (2 * m : ℝ) * R ^ (m - 1) * D * R ^ m := by
    exact norm_lowerConjugateMomentDerivative_le m _ _ (by positivity) hw hdw
  have hA :
      ‖sourceInverse (coordinateMatrix v.2 q₀.1.1 q₀.1.2 v.1.1 v.1.2) z i q₀.1.1 *
            sourceInverse (coordinateMatrix v.2 q₀.1.1 q₀.1.2 v.1.1 v.1.2) z q₀.1.2 j +
          sourceInverse (coordinateMatrix v.2 q₀.1.1 q₀.1.2 v.1.1 v.1.2) z i q₀.1.2 *
            sourceInverse (coordinateMatrix v.2 q₀.1.1 q₀.1.2 v.1.1 v.1.2) z q₀.1.1 j‖ ≤
        E * E + E * E := by
    calc
      _ ≤ ‖sourceInverse (coordinateMatrix v.2 q₀.1.1 q₀.1.2 v.1.1 v.1.2) z i q₀.1.1 *
            sourceInverse (coordinateMatrix v.2 q₀.1.1 q₀.1.2 v.1.1 v.1.2) z q₀.1.2 j‖ +
          ‖sourceInverse (coordinateMatrix v.2 q₀.1.1 q₀.1.2 v.1.1 v.1.2) z i q₀.1.2 *
            sourceInverse (coordinateMatrix v.2 q₀.1.1 q₀.1.2 v.1.1 v.1.2) z q₀.1.1 j‖ :=
        norm_add_le _ _
      _ ≤ _ := by
        rw [norm_mul, norm_mul]
        exact add_le_add
          (mul_le_mul (hG i q₀.1.1) (hG q₀.1.2 j) (norm_nonneg _) hE)
          (mul_le_mul (hG i q₀.1.2) (hG q₀.1.1 j) (norm_nonneg _) hE)
  rw [coordinateResolventLowerDerivReal]
  calc
    _ ≤ ‖-(sourceInverse (coordinateMatrix v.2 q₀.1.1 q₀.1.2 v.1.1 v.1.2) z i q₀.1.1 *
            sourceInverse (coordinateMatrix v.2 q₀.1.1 q₀.1.2 v.1.1 v.1.2) z q₀.1.2 j +
          sourceInverse (coordinateMatrix v.2 q₀.1.1 q₀.1.2 v.1.1 v.1.2) z i q₀.1.2 *
            sourceInverse (coordinateMatrix v.2 q₀.1.1 q₀.1.2 v.1.1 v.1.2) z q₀.1.1 j) *
          lowerConjugateMomentTest m
            (coordinateSignedError p v.2 q₀.1.1 q₀.1.2 x y z v.1.1 v.1.2)‖ +
        ‖sourceInverse (coordinateMatrix v.2 q₀.1.1 q₀.1.2 v.1.1 v.1.2) z i j *
          lowerConjugateMomentDerivative m
            (coordinateSignedError p v.2 q₀.1.1 q₀.1.2 x y z v.1.1 v.1.2)
            (coordinateSignedErrorDerivReal p v.2 q₀.1.1 q₀.1.2 x y z v.1.1 v.1.2)‖ :=
      norm_add_le _ _
    _ ≤ ((E * E + E * E) * R ^ (2 * m)) +
        E * ((2 * m : ℝ) * R ^ (m - 1) * D * R ^ m) := by
      rw [norm_mul, norm_neg, norm_mul]
      exact add_le_add
        (mul_le_mul hA hL (norm_nonneg _)
          (add_nonneg (mul_nonneg hE hE) (mul_nonneg hE hE)))
        (mul_le_mul (hG i j) hdL (norm_nonneg _) hE)
    _ = resolventWeightedDerivativeBound z m := by
      simp only [resolventWeightedDerivativeBound, E, C, R, D]
      ring

/-- The full imaginary derivative has the same uniform bound. -/
theorem Law.ae_norm_coordinateResolventLowerDerivImaginary_le
    {p : Params} (M : Law p) (q₀ : UpperPair p)
    (hne : q₀.1.1 ≠ q₀.1.2) (x y i j : Site p.n p.W)
    (z : ℂ) (hz : 0 < z.im) (m : ℕ) :
    ∀ᵐ v ∂strictCoordinateProductMeasure M q₀,
      ‖coordinateResolventLowerDerivImaginary p v.2 q₀.1.1 q₀.1.2
          x y i j z m v.1.1 v.1.2‖ ≤
        resolventWeightedDerivativeBound z m := by
  filter_upwards [Law.strictCoordinateProduct_ae_isHermitian M q₀ hne] with v hB
  let E := (z.im)⁻¹
  let C := E + ‖erSemicircleStieltjes z‖
  let R := max 1 C
  let D := 2 * E ^ 2
  have hE : 0 ≤ E := inv_nonneg.mpr hz.le
  have hG (u w : Site p.n p.W) :
      ‖sourceInverse (coordinateMatrix v.2 q₀.1.1 q₀.1.2
        v.1.1 v.1.2) z u w‖ ≤ E :=
    norm_sourceInverse_coordinate_le v.2 hB q₀.1.1 q₀.1.2
      u w z hz v.1.1 v.1.2
  have hw : ‖coordinateSignedError p v.2 q₀.1.1 q₀.1.2
      x y z v.1.1 v.1.2‖ ≤ C :=
    norm_coordinateSignedError_le p v.2 hB q₀.1.1 q₀.1.2
      x y z hz v.1.1 v.1.2
  have hdw : ‖coordinateSignedErrorDerivImaginary p v.2 q₀.1.1 q₀.1.2
      x y z v.1.1 v.1.2‖ ≤ D :=
    norm_coordinateSignedErrorDerivImaginary_le p v.2 hB q₀.1.1 q₀.1.2
      x y z hz v.1.1 v.1.2
  have hL : ‖lowerConjugateMomentTest m
      (coordinateSignedError p v.2 q₀.1.1 q₀.1.2
        x y z v.1.1 v.1.2)‖ ≤ R ^ (2 * m) := by
    rw [norm_lowerConjugateMomentTest]
    exact pow_le_pow_left₀ (norm_nonneg _) (hw.trans (le_max_right _ _)) _
  have hdL : ‖lowerConjugateMomentDerivative m
      (coordinateSignedError p v.2 q₀.1.1 q₀.1.2
        x y z v.1.1 v.1.2)
      (coordinateSignedErrorDerivImaginary p v.2 q₀.1.1 q₀.1.2
        x y z v.1.1 v.1.2)‖ ≤
      (2 * m : ℝ) * R ^ (m - 1) * D * R ^ m := by
    exact norm_lowerConjugateMomentDerivative_le m _ _ (by positivity) hw hdw
  have hA :
      ‖-Complex.I * sourceInverse (coordinateMatrix v.2 q₀.1.1 q₀.1.2 v.1.1 v.1.2) z i q₀.1.1 *
            sourceInverse (coordinateMatrix v.2 q₀.1.1 q₀.1.2 v.1.1 v.1.2) z q₀.1.2 j +
          Complex.I * sourceInverse (coordinateMatrix v.2 q₀.1.1 q₀.1.2 v.1.1 v.1.2) z i q₀.1.2 *
            sourceInverse (coordinateMatrix v.2 q₀.1.1 q₀.1.2 v.1.1 v.1.2) z q₀.1.1 j‖ ≤
        E * E + E * E := by
    calc
      _ ≤ ‖-Complex.I * sourceInverse (coordinateMatrix v.2 q₀.1.1 q₀.1.2 v.1.1 v.1.2) z i q₀.1.1 *
            sourceInverse (coordinateMatrix v.2 q₀.1.1 q₀.1.2 v.1.1 v.1.2) z q₀.1.2 j‖ +
          ‖Complex.I * sourceInverse (coordinateMatrix v.2 q₀.1.1 q₀.1.2 v.1.1 v.1.2) z i q₀.1.2 *
            sourceInverse (coordinateMatrix v.2 q₀.1.1 q₀.1.2 v.1.1 v.1.2) z q₀.1.1 j‖ :=
        norm_add_le _ _
      _ ≤ _ := by
        simp only [norm_mul, norm_neg, Complex.norm_I, one_mul]
        exact add_le_add
          (mul_le_mul (hG i q₀.1.1) (hG q₀.1.2 j) (norm_nonneg _) hE)
          (mul_le_mul (hG i q₀.1.2) (hG q₀.1.1 j) (norm_nonneg _) hE)
  rw [coordinateResolventLowerDerivImaginary]
  calc
    _ ≤ ‖(-Complex.I * sourceInverse (coordinateMatrix v.2 q₀.1.1 q₀.1.2 v.1.1 v.1.2) z i q₀.1.1 *
            sourceInverse (coordinateMatrix v.2 q₀.1.1 q₀.1.2 v.1.1 v.1.2) z q₀.1.2 j +
          Complex.I * sourceInverse (coordinateMatrix v.2 q₀.1.1 q₀.1.2 v.1.1 v.1.2) z i q₀.1.2 *
            sourceInverse (coordinateMatrix v.2 q₀.1.1 q₀.1.2 v.1.1 v.1.2) z q₀.1.1 j) *
          lowerConjugateMomentTest m
            (coordinateSignedError p v.2 q₀.1.1 q₀.1.2 x y z v.1.1 v.1.2)‖ +
        ‖sourceInverse (coordinateMatrix v.2 q₀.1.1 q₀.1.2 v.1.1 v.1.2) z i j *
          lowerConjugateMomentDerivative m
            (coordinateSignedError p v.2 q₀.1.1 q₀.1.2 x y z v.1.1 v.1.2)
            (coordinateSignedErrorDerivImaginary p v.2 q₀.1.1 q₀.1.2 x y z v.1.1 v.1.2)‖ :=
      norm_add_le _ _
    _ ≤ ((E * E + E * E) * R ^ (2 * m)) +
        E * ((2 * m : ℝ) * R ^ (m - 1) * D * R ^ m) := by
      rw [norm_mul, norm_mul]
      exact add_le_add
        (mul_le_mul hA hL (norm_nonneg _)
          (add_nonneg (mul_nonneg hE hE) (mul_nonneg hE hE)))
        (mul_le_mul (hG i j) hdL (norm_nonneg _) hE)
    _ = resolventWeightedDerivativeBound z m := by
      simp only [resolventWeightedDerivativeBound, E, C, R, D]
      ring

/-- The undifferentiated resolvent-weighted test is integrable on the full
strict coordinate product. -/
theorem Law.integrable_coordinateResolventLowerTest_product
    {p : Params} (M : Law p) (q₀ : UpperPair p)
    (hne : q₀.1.1 ≠ q₀.1.2) (x y i j : Site p.n p.W)
    (z : ℂ) (hz : 0 < z.im) (m : ℕ) :
    Integrable (fun v => coordinateResolventLowerTest p v.2 q₀.1.1 q₀.1.2
      x y i j z m v.1.1 v.1.2) (strictCoordinateProductMeasure M q₀) := by
  let _ : IsFiniteMeasure (strictBackgroundMeasure M q₀) :=
    Measure.isFiniteMeasure_map M.P _
  let _ : IsFiniteMeasure (circularGaussianMeasure
      ⟨siteCovariance p q₀.1.1 q₀.1.2,
        (siteCovariance_flat p q₀.1.1 q₀.1.2).1⟩) :=
    circularGaussianMeasure_isFinite _
  let _ : IsFiniteMeasure (strictCoordinateProductMeasure M q₀) :=
    Measure.prod.instIsFiniteMeasure _ _
  exact Integrable.of_bound
    (measurable_coordinateResolventLowerTest_product p q₀.1.1 q₀.1.2
      x y i j z m).aestronglyMeasurable
    ((z.im)⁻¹ * ((z.im)⁻¹ + ‖erSemicircleStieltjes z‖) ^ (2 * m))
    (Law.ae_norm_coordinateResolventLowerTest_le M q₀ hne x y i j z hz m)

/-- The full real derivative test is integrable on the product. -/
theorem Law.integrable_coordinateResolventLowerDerivReal_product
    {p : Params} (M : Law p) (q₀ : UpperPair p)
    (hne : q₀.1.1 ≠ q₀.1.2) (x y i j : Site p.n p.W)
    (z : ℂ) (hz : 0 < z.im) (m : ℕ) :
    Integrable (fun v => coordinateResolventLowerDerivReal p v.2
      q₀.1.1 q₀.1.2 x y i j z m v.1.1 v.1.2)
      (strictCoordinateProductMeasure M q₀) := by
  let _ : IsFiniteMeasure (strictBackgroundMeasure M q₀) :=
    Measure.isFiniteMeasure_map M.P _
  let _ : IsFiniteMeasure (circularGaussianMeasure
      ⟨siteCovariance p q₀.1.1 q₀.1.2,
        (siteCovariance_flat p q₀.1.1 q₀.1.2).1⟩) :=
    circularGaussianMeasure_isFinite _
  let _ : IsFiniteMeasure (strictCoordinateProductMeasure M q₀) :=
    Measure.prod.instIsFiniteMeasure _ _
  exact Integrable.of_bound
    (measurable_coordinateResolventLowerDerivReal_product p q₀.1.1 q₀.1.2
      x y i j z m).aestronglyMeasurable
    (resolventWeightedDerivativeBound z m)
    (Law.ae_norm_coordinateResolventLowerDerivReal_le
      M q₀ hne x y i j z hz m)

/-- The full imaginary derivative test is integrable on the product. -/
theorem Law.integrable_coordinateResolventLowerDerivImaginary_product
    {p : Params} (M : Law p) (q₀ : UpperPair p)
    (hne : q₀.1.1 ≠ q₀.1.2) (x y i j : Site p.n p.W)
    (z : ℂ) (hz : 0 < z.im) (m : ℕ) :
    Integrable (fun v => coordinateResolventLowerDerivImaginary p v.2
      q₀.1.1 q₀.1.2 x y i j z m v.1.1 v.1.2)
      (strictCoordinateProductMeasure M q₀) := by
  let _ : IsFiniteMeasure (strictBackgroundMeasure M q₀) :=
    Measure.isFiniteMeasure_map M.P _
  let _ : IsFiniteMeasure (circularGaussianMeasure
      ⟨siteCovariance p q₀.1.1 q₀.1.2,
        (siteCovariance_flat p q₀.1.1 q₀.1.2).1⟩) :=
    circularGaussianMeasure_isFinite _
  let _ : IsFiniteMeasure (strictCoordinateProductMeasure M q₀) :=
    Measure.prod.instIsFiniteMeasure _ _
  exact Integrable.of_bound
    (measurable_coordinateResolventLowerDerivImaginary_product p
      q₀.1.1 q₀.1.2 x y i j z m).aestronglyMeasurable
    (resolventWeightedDerivativeBound z m)
    (Law.ae_norm_coordinateResolventLowerDerivImaginary_le
      M q₀ hne x y i j z hz m)

/-- The real-coordinate-weighted resolvent/lower-moment test is integrable on
the full strict product. -/
theorem Law.integrable_realWeightedCoordinateResolventLowerTest_product
    {p : Params} (M : Law p) (q₀ : UpperPair p)
    (hne : q₀.1.1 ≠ q₀.1.2) (x y i j : Site p.n p.W)
    (z : ℂ) (hz : 0 < z.im) (m : ℕ) :
    Integrable (fun v => (v.1.1 : ℂ) *
      coordinateResolventLowerTest p v.2 q₀.1.1 q₀.1.2
        x y i j z m v.1.1 v.1.2)
      (strictCoordinateProductMeasure M q₀) := by
  apply (Law.integrable_realCoordinate_product M q₀).mul_bdd
    (measurable_coordinateResolventLowerTest_product p q₀.1.1 q₀.1.2
      x y i j z m).aestronglyMeasurable
  exact Law.ae_norm_coordinateResolventLowerTest_le M q₀ hne
    x y i j z hz m

/-- Imaginary-coordinate counterpart of the weighted-test integrability. -/
theorem Law.integrable_imaginaryWeightedCoordinateResolventLowerTest_product
    {p : Params} (M : Law p) (q₀ : UpperPair p)
    (hne : q₀.1.1 ≠ q₀.1.2) (x y i j : Site p.n p.W)
    (z : ℂ) (hz : 0 < z.im) (m : ℕ) :
    Integrable (fun v => (v.1.2 : ℂ) *
      coordinateResolventLowerTest p v.2 q₀.1.1 q₀.1.2
        x y i j z m v.1.1 v.1.2)
      (strictCoordinateProductMeasure M q₀) := by
  apply (Law.integrable_imaginaryCoordinate_product M q₀).mul_bdd
    (measurable_coordinateResolventLowerTest_product p q₀.1.1 q₀.1.2
      x y i j z m).aestronglyMeasurable
  exact Law.ae_norm_coordinateResolventLowerTest_le M q₀ hne
    x y i j z hz m

end ERSharpCoordinateIBP
end GaussianRing
end ERNative.BlockBand
