module

public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.SharpCoordinateTransfer

/-!
# Product integrability for the sharp ER coordinate IBP

Small named lemmas in this module establish joint measurability and domination
on the two-Gaussian-coordinate/background product.  They are deliberately
separated so elaboration never expands all resolvent and conjugate-moment
expressions in one tactic call.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace ERNative.BlockBand
namespace GaussianRing
namespace ERSharpCoordinateIBP

open Matrix MeasureTheory ProbabilityTheory
open ERGaussianCoordinate ERResolventMomentIBP ERProfile
open ERComplementBackgroundReconstruction
open scoped BigOperators NNReal

local instance (p : Params) : NeZero p.n := p.nNeZero
local instance (p : Params) : Finite (UpperPair p) :=
  Finite.of_injective Subtype.val Subtype.val_injective
local instance (p : Params) : Fintype (UpperPair p) := Fintype.ofFinite _
local instance (p : Params) : DecidableEq (UpperPair p) := Classical.decEq _

/-- Background marginal for one removed strict coordinate. -/
def strictBackgroundMeasure {p : Params} (M : Law p) (q₀ : UpperPair p) :
    Measure (Matrix (Site p.n p.W) (Site p.n p.W) ℂ) :=
  M.P.map (fun ω => offdiagBackground (M.H ω) q₀.1.1 q₀.1.2)

/-- Exact two-real-Gaussian/background product measure for a strict entry. -/
def strictCoordinateProductMeasure {p : Params} (M : Law p) (q₀ : UpperPair p) :
    Measure ((ℝ × ℝ) × Matrix (Site p.n p.W) (Site p.n p.W) ℂ) :=
  (circularGaussianMeasure
    ⟨siteCovariance p q₀.1.1 q₀.1.2,
      (siteCovariance_flat p q₀.1.1 q₀.1.2).1⟩).prod
    (strictBackgroundMeasure M q₀)

/-- The circular two-coordinate Gaussian measure is finite, including at
zero variance. -/
theorem circularGaussianMeasure_isFinite (t : NNReal) :
    IsFiniteMeasure (circularGaussianMeasure t) := by
  let _ : IsProbabilityMeasure (gaussianReal 0 (t / 2)) :=
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
  let _ : IsFiniteMeasure (gaussianReal 0 (t / 2)) :=
    ⟨by rw [IsProbabilityMeasure.measure_univ]; norm_num⟩
  rw [circularGaussianMeasure]
  exact Measure.prod.instIsFiniteMeasure _ _

/-- At zero covariance the two-coordinate circular Gaussian is the Dirac
mass at the zero pair. -/
theorem circularGaussianMeasure_zero :
    circularGaussianMeasure 0 = Measure.dirac (0, 0) := by
  rw [circularGaussianMeasure]
  simp only [zero_div, gaussianReal_zero_var]
  exact Measure.dirac_prod_dirac

/-- Joint measurability of the real coordinate derivative on the complete
coordinate/background space. -/
theorem measurable_coordinateSignedErrorDerivReal_product
    (p : Params) (a b x y : Site p.n p.W) (z : ℂ) :
    Measurable (fun v : (ℝ × ℝ) ×
      Matrix (Site p.n p.W) (Site p.n p.W) ℂ =>
        coordinateSignedErrorDerivReal p v.2 a b x y z v.1.1 v.1.2) := by
  unfold coordinateSignedErrorDerivReal
  apply Measurable.neg
  apply Finset.measurable_sum
  intro k _
  exact measurable_const.mul
    (((measurable_sourceInverse_productEntry p a b k a z).mul
      (measurable_sourceInverse_productEntry p a b b y z)).add
     ((measurable_sourceInverse_productEntry p a b k b z).mul
      (measurable_sourceInverse_productEntry p a b a y z)))

/-- Joint measurability of the imaginary coordinate derivative. -/
theorem measurable_coordinateSignedErrorDerivImaginary_product
    (p : Params) (a b x y : Site p.n p.W) (z : ℂ) :
    Measurable (fun v : (ℝ × ℝ) ×
      Matrix (Site p.n p.W) (Site p.n p.W) ℂ =>
        coordinateSignedErrorDerivImaginary p v.2 a b x y z v.1.1 v.1.2) := by
  unfold coordinateSignedErrorDerivImaginary
  apply Finset.measurable_sum
  intro k _
  exact measurable_const.mul
    (((measurable_const.mul
      (measurable_sourceInverse_productEntry p a b k a z)).mul
      (measurable_sourceInverse_productEntry p a b b y z)).add
     ((measurable_const.mul
      (measurable_sourceInverse_productEntry p a b k b z)).mul
      (measurable_sourceInverse_productEntry p a b a y z)))

/-- Hermitian support lifts from the background marginal to the full strict
coordinate product. -/
theorem Law.strictCoordinateProduct_ae_isHermitian
    {p : Params} (M : Law p) (q₀ : UpperPair p)
    (hne : q₀.1.1 ≠ q₀.1.2) :
    ∀ᵐ v ∂strictCoordinateProductMeasure M q₀, v.2.IsHermitian := by
  let _ : IsFiniteMeasure (strictBackgroundMeasure M q₀) :=
    Measure.isFiniteMeasure_map M.P _
  have hentry : Measurable
      (fun v : (ℝ × ℝ) × Matrix (Site p.n p.W) (Site p.n p.W) ℂ =>
        ∀ i j, starRingEnd ℂ (v.2 j i) = v.2 i j) := by
    apply Measurable.forall
    intro i
    apply Measurable.forall
    intro j
    exact (Complex.continuous_conj.measurable.comp
      (Matrix.measurable_apply.comp measurable_snd)).eq
        (Matrix.measurable_apply.comp measurable_snd)
  have hae : ∀ᵐ v ∂strictCoordinateProductMeasure M q₀,
      ∀ i j, starRingEnd ℂ (v.2 j i) = v.2 i j := by
    apply (Measure.ae_prod_iff_ae_ae hentry.setOf).2
    filter_upwards [] with rs
    filter_upwards [Law.offdiagBackground_ae_isHermitian M q₀ hne] with B hB
    intro i j
    exact congrFun (congrFun hB i) j
  filter_upwards [hae] with v hv
  ext i j
  exact hv i j

/-- The real Gaussian coordinate, viewed as a complex-valued function, is
integrable on the full coordinate/background product. -/
theorem Law.integrable_realCoordinate_product
    {p : Params} (M : Law p) (q₀ : UpperPair p) :
    Integrable (fun v :
      (ℝ × ℝ) × Matrix (Site p.n p.W) (Site p.n p.W) ℂ =>
        (v.1.1 : ℂ)) (strictCoordinateProductMeasure M q₀) := by
  let t : NNReal :=
    ⟨siteCovariance p q₀.1.1 q₀.1.2,
      (siteCovariance_flat p q₀.1.1 q₀.1.2).1⟩
  let _ : IsProbabilityMeasure (gaussianReal 0 (t / 2)) :=
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
  let _ : IsFiniteMeasure (gaussianReal 0 (t / 2)) :=
    ⟨by rw [IsProbabilityMeasure.measure_univ]; norm_num⟩
  let _ : IsFiniteMeasure (strictBackgroundMeasure M q₀) :=
    Measure.isFiniteMeasure_map M.P _
  have hr : Integrable (fun r : ℝ => (r : ℂ)) (gaussianReal 0 (t / 2)) :=
    ((memLp_id_gaussianReal (μ := 0) (v := t / 2) 1).integrable
      (by norm_num)).ofReal
  have hrs : Integrable (fun rs : ℝ × ℝ => (rs.1 : ℂ))
      (circularGaussianMeasure t) := by
    rw [circularGaussianMeasure]
    exact hr.comp_fst _
  simpa [strictCoordinateProductMeasure, t] using
    hrs.comp_fst (strictBackgroundMeasure M q₀)

/-- The imaginary Gaussian coordinate is integrable on the same full
product. -/
theorem Law.integrable_imaginaryCoordinate_product
    {p : Params} (M : Law p) (q₀ : UpperPair p) :
    Integrable (fun v :
      (ℝ × ℝ) × Matrix (Site p.n p.W) (Site p.n p.W) ℂ =>
        (v.1.2 : ℂ)) (strictCoordinateProductMeasure M q₀) := by
  let t : NNReal :=
    ⟨siteCovariance p q₀.1.1 q₀.1.2,
      (siteCovariance_flat p q₀.1.1 q₀.1.2).1⟩
  let _ : IsProbabilityMeasure (gaussianReal 0 (t / 2)) :=
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
  let _ : IsFiniteMeasure (gaussianReal 0 (t / 2)) :=
    ⟨by rw [IsProbabilityMeasure.measure_univ]; norm_num⟩
  let _ : IsFiniteMeasure (strictBackgroundMeasure M q₀) :=
    Measure.isFiniteMeasure_map M.P _
  have hs : Integrable (fun s : ℝ => (s : ℂ)) (gaussianReal 0 (t / 2)) :=
    ((memLp_id_gaussianReal (μ := 0) (v := t / 2) 1).integrable
      (by norm_num)).ofReal
  have hrs : Integrable (fun rs : ℝ × ℝ => (rs.2 : ℂ))
      (circularGaussianMeasure t) := by
    rw [circularGaussianMeasure]
    exact hs.comp_snd _
  simpa [strictCoordinateProductMeasure, t] using
    hrs.comp_fst (strictBackgroundMeasure M q₀)

end ERSharpCoordinateIBP
end GaussianRing
end ERNative.BlockBand
