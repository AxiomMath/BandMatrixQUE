module

public import BlockBand.DeterminantScore.GaussianPolynomialGradient.CircleWeightedEstimate
public import BlockBand.DeterminantScore.GaussianPolynomialGradient.PolynomialRotationBridge
public import BlockBand.DeterminantScore.GaussianPolynomialGradient.GaussianRotationMoments

/-!
# The Gaussian polynomial gradient estimate

For `2 ≤ p < 3` and a degree bound `k` there is a constant `C`, independent of the dimension and of
the coefficients, such that every nonzero real polynomial `P` of degree at most `k` on a finite
dimensional Euclidean space satisfies
`E |∇P|^p |P|^{2-p} ≤ C E P²` under the standard Gaussian measure
(`exists_gaussian_polynomial_gradient_constant`). The proof averages over rotations of an
independent Gaussian pair, `X cos θ + Y sin θ`, which reduces the estimate to the weighted
polynomial estimate on the unit circle (`circleAverage_weightedAngular_le`) applied to the
restriction of `P`, and computes the directional moment `E |⟨∇P, Y⟩|^p` by the normal moment.
-/
universe u

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.DeterminantScore.GaussianGradient
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators ENNReal NNReal InnerProductSpace
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Evaluation of a polynomial on Euclidean coordinates. -/
def polynomialValue (P : MvPolynomial ι ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  MvPolynomial.eval (fun i => x i) P

/-- The Euclidean gradient of a polynomial, from its partial derivatives. -/
def euclideanPolynomialGradient (P : MvPolynomial ι ℝ) (x : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι := polynomialGradient P (fun i => x i)

omit [DecidableEq ι] in
/-- The polynomial value is continuous. -/
theorem continuous_polynomialValue (P : MvPolynomial ι ℝ) : Continuous (polynomialValue P) := by
  unfold polynomialValue
  rw [show (fun x : EuclideanSpace ℝ ι => MvPolynomial.eval (fun i => x i) P) =
    fun x => ∑ s ∈ P.support, P.coeff s * ∏ i, x i ^ s i by
      funext x; exact MvPolynomial.eval_eq' _ P]
  fun_prop

omit [DecidableEq ι] in
/-- The gradient is continuous. -/
theorem continuous_euclideanPolynomialGradient (P : MvPolynomial ι ℝ) :
    Continuous (euclideanPolynomialGradient P) := by
  unfold euclideanPolynomialGradient polynomialGradient
  apply (PiLp.continuous_toLp 2 (fun _ : ι => ℝ)).comp
  apply continuous_pi
  intro i
  exact continuous_polynomialValue (MvPolynomial.pderiv i P)

omit [DecidableEq ι] in
/-- `P²` is integrable under `stdGaussian`. -/
theorem integrable_polynomialValue_sq (P : MvPolynomial ι ℝ) :
    Integrable (fun x : EuclideanSpace ℝ ι => polynomialValue P x ^ 2)
      (stdGaussian (EuclideanSpace ℝ ι)) := by
  rw [← standardGaussianCoordinates_toLp]
  apply (integrable_map_measure ((continuous_polynomialValue P).pow 2).aestronglyMeasurable
    (PiLp.continuous_toLp 2 (fun _ : ι => ℝ)).measurable.aemeasurable).mpr
  exact integrable_polynomial_sq_standardGaussian P

/-- The normalized circle-angle law on one half-open period. -/
def normalizedCircleAngles : Measure ℝ :=
  (ENNReal.ofReal (2 * Real.pi))⁻¹ • volume.restrict (Set.Ioc 0 (2 * Real.pi))

omit [Fintype ι] [DecidableEq ι] in
/-- The normalized angular law has total mass one. -/
theorem normalizedCircleAngles_univ : normalizedCircleAngles Set.univ = 1 := by
  simp only [normalizedCircleAngles, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]
  exact ENNReal.inv_mul_cancel (by positivity) ENNReal.ofReal_ne_top

omit [Fintype ι] [DecidableEq ι] in
/-- The nonnegative normalized-angle integral equals `ofReal` of `circleAverage` when the real
circle integrand is integrable and nonnegative. -/
theorem lintegral_normalizedCircleAngles (f : ℂ → ℝ) (hf : CircleIntegrable f 0 1)
    (hn : ∀ z : ℂ, 0 ≤ f z) :
    (∫⁻ θ : ℝ, ENNReal.ofReal (f (circleMap 0 1 θ)) ∂normalizedCircleAngles) =
      ENNReal.ofReal (Real.circleAverage f 0 1) := by
  have hT : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hfi := (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp hf
  rw [normalizedCircleAngles, lintegral_smul_measure,
    ← ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall (fun θ => hn _))]
  simp only [Real.circleAverage_def, smul_eq_mul]
  rw [intervalIntegral.integral_of_le hT]
  conv_rhs => rw [ENNReal.ofReal_mul (by positivity)]
  rw [ENNReal.ofReal_inv_of_pos (by positivity)]

instance normalizedCircleAngles_probability : IsProbabilityMeasure normalizedCircleAngles :=
  ⟨normalizedCircleAngles_univ⟩

omit [DecidableEq ι] in
/-- Tonelli rotation averaging on the normalized circle. The function may have infinite integral;
only measurability is assumed. -/
theorem lintegral_pair_rotation_average (F : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι → ℝ≥0∞)
    (hF : Measurable F) :
    (∫⁻ q, ∫⁻ θ : ℝ, F (ContinuousLinearMap.rotation θ q) ∂normalizedCircleAngles
      ∂(stdGaussian (EuclideanSpace ℝ ι)).prod (stdGaussian (EuclideanSpace ℝ ι))) =
      ∫⁻ q, F q ∂(stdGaussian (EuclideanSpace ℝ ι)).prod (stdGaussian (EuclideanSpace ℝ ι)) := by
  have hj : Measurable (Function.uncurry
      (fun q : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => fun θ : ℝ =>
        F (ContinuousLinearMap.rotation θ q))) := by
    apply hF.comp
    simp only [ContinuousLinearMap.rotation_apply]
    fun_prop
  rw [lintegral_lintegral_swap hj.aemeasurable]
  simp_rw [lintegral_standardGaussianPair_rotation F hF]
  simp

/-- The weighted directional moment `|⟨∇P(X), Y⟩|^p |P(X)|^{2-p}` on the Gaussian pair. -/
def pairWeighted (P : MvPolynomial ι ℝ) (p : ℝ)
    (q : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) : ℝ≥0∞ :=
  ENNReal.ofReal (‖⟪euclideanPolynomialGradient P q.1, q.2⟫_ℝ‖ ^ p *
    ‖polynomialValue P q.1‖ ^ (2 - p))

omit [DecidableEq ι] in
/-- The pair weighted integrand is measurable. -/
theorem measurable_pairWeighted (P : MvPolynomial ι ℝ) (p : ℝ) : Measurable (pairWeighted P p) := by
  have hg := continuous_euclideanPolynomialGradient P
  have hv := continuous_polynomialValue P
  have hinner : Measurable (fun q : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
      ‖⟪euclideanPolynomialGradient P q.1, q.2⟫_ℝ‖) := by fun_prop
  have hvalue : Measurable (fun q : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
      ‖polynomialValue P q.1‖) := by fun_prop
  exact ENNReal.measurable_ofReal.comp ((hinner.pow_const p).mul (hvalue.pow_const (2 - p)))

/-- The square mass `P(X)²` on the Gaussian pair. -/
def pairSquare (P : MvPolynomial ι ℝ)
    (q : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) : ℝ≥0∞ :=
  ENNReal.ofReal (polynomialValue P q.1 ^ 2)

omit [DecidableEq ι] in
/-- The pair square integrand is measurable. -/
theorem measurable_pairSquare (P : MvPolynomial ι ℝ) : Measurable (pairSquare P) := by
  exact ENNReal.measurable_ofReal.comp (((continuous_polynomialValue P).comp continuous_fst).pow 2).measurable

omit [DecidableEq ι] in
/-- The value of `P` at the rotated point `X cos θ + Y sin θ` is the coordinate polynomial curve. -/
theorem polynomialValue_rotation (P : MvPolynomial ι ℝ)
    (q : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) (θ : ℝ) :
    polynomialValue P (ContinuousLinearMap.rotation θ q).1 =
      MvPolynomial.eval (rotatedCoordinates (fun i => q.1 i) (fun i => q.2 i) θ) P := by
  rfl

omit [DecidableEq ι] in
/-- The Gaussian directional pairing equals the derivative of the rotated polynomial curve. -/
theorem polynomial_inner_rotation (P : MvPolynomial ι ℝ)
    (q : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) (θ : ℝ) :
    ⟪euclideanPolynomialGradient P (ContinuousLinearMap.rotation θ q).1,
      (ContinuousLinearMap.rotation θ q).2⟫_ℝ =
      polynomialDirectional P
        (rotatedCoordinates (fun i => q.1 i) (fun i => q.2 i) θ)
        (rotatedVelocity (fun i => q.1 i) (fun i => q.2 i) θ) := by
  simp [euclideanPolynomialGradient, polynomialGradient, PiLp.inner_apply,
    polynomialDirectional, ContinuousLinearMap.rotation_apply, rotatedVelocity, mul_comm]
  rfl

omit [DecidableEq ι] in
/-- The absolute value of the circle restriction equals the absolute value of the rotated
polynomial. -/
theorem restriction_norm_eq_rotation (P : MvPolynomial ι ℝ) (k : ℕ)
    (hP : P.totalDegree ≤ k) (q : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) (θ : ℝ) :
    ‖(circleRestriction P k (fun i => q.1 i) (fun i => q.2 i)).eval (circleMap 0 1 θ)‖ =
      ‖polynomialValue P (ContinuousLinearMap.rotation θ q).1‖ := by
  rw [show circleMap 0 1 θ = Complex.exp (θ * Complex.I) by simp [circleMap],
    circleRestriction_eval_circle P k (fun i => q.1 i) (fun i => q.2 i) hP θ]
  simp [norm_pow, polynomialValue_rotation]
  rfl

/-- The rotated weighted Gaussian integrand is the weighted circle integrand of the degree-`2k`
circle restriction. -/
theorem pairWeighted_rotation_eq_circle (P : MvPolynomial ι ℝ) (k : ℕ) (p : ℝ)
    (hP : P.totalDegree ≤ k) (q : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) (θ : ℝ) :
    pairWeighted P p (ContinuousLinearMap.rotation θ q) =
      ENNReal.ofReal (weightedAngular (circleRestriction P k (fun i => q.1 i) (fun i => q.2 i))
        k p (circleMap 0 1 θ)) := by
  unfold pairWeighted weightedAngular
  have ha := circleRestriction_angular_norm P k (fun i => q.1 i) (fun i => q.2 i) hP θ
  have ha' : ‖angularNumerator (circleRestriction P k (fun i => q.1 i) (fun i => q.2 i))
      k (circleMap 0 1 θ)‖ = ‖⟪euclideanPolynomialGradient P (ContinuousLinearMap.rotation θ q).1,
        (ContinuousLinearMap.rotation θ q).2⟫_ℝ‖ := by
    rw [polynomial_inner_rotation]
    simpa only [angularNumerator, circleMap, Complex.ofReal_one, one_mul, zero_add] using ha
  rw [ha', restriction_norm_eq_rotation P k hP q θ]

omit [DecidableEq ι] in
/-- The rotated square integrand is the circle `L²` value of the restriction. -/
theorem pairSquare_rotation_eq_circle (P : MvPolynomial ι ℝ) (k : ℕ)
    (hP : P.totalDegree ≤ k) (q : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) (θ : ℝ) :
    pairSquare P (ContinuousLinearMap.rotation θ q) =
      ENNReal.ofReal (‖(circleRestriction P k (fun i => q.1 i) (fun i => q.2 i)).eval
        (circleMap 0 1 θ)‖ ^ 2) := by
  rw [restriction_norm_eq_rotation P k hP q θ]
  simp [pairSquare, Real.norm_eq_abs]

omit [Fintype ι] [DecidableEq ι] in
/-- The weighted circle constant is nonnegative for `2 ≤ p < 3`. -/
theorem weightedCircleConstant_nonneg (k m : ℕ) (p : ℝ) (hp2 : 2 ≤ p) (hp3 : p < 3) :
    0 ≤ weightedCircleConstant k m p := by
  unfold weightedCircleConstant quotientCoercivity
  exact mul_nonneg (Real.rpow_nonneg (by positivity) (p - 1))
    (add_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) p)
      (mul_nonneg (by positivity) (circleKernelMajorant_nonneg (p - 2) (by linarith) (by linarith))))

/-- The circle estimate applied to every Gaussian vector pair. -/
theorem pair_circle_estimate (P : MvPolynomial ι ℝ) (k : ℕ) (p : ℝ)
    (hP : P.totalDegree ≤ k) (hp2 : 2 ≤ p) (hp3 : p < 3)
    (q : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    (∫⁻ θ : ℝ, pairWeighted P p (ContinuousLinearMap.rotation θ q) ∂normalizedCircleAngles) ≤
      ENNReal.ofReal (weightedCircleConstant k (2 * k) p) *
        (∫⁻ θ : ℝ, pairSquare P (ContinuousLinearMap.rotation θ q) ∂normalizedCircleAngles) := by
  let Q := circleRestriction P k (fun i => q.1 i) (fun i => q.2 i)
  have hd : Q.natDegree ≤ 2 * k := circleRestriction_natDegree_le P k _ _ hP
  simp_rw [pairWeighted_rotation_eq_circle P k p hP q,
    pairSquare_rotation_eq_circle P k hP q]
  rw [lintegral_normalizedCircleAngles (weightedAngular Q k p)
      (circleIntegrable_weightedAngular Q k (2 * k) p hd hp2 hp3) (weightedAngular_nonneg Q k p),
    lintegral_normalizedCircleAngles (fun z => ‖Q.eval z‖ ^ 2)
      (circleIntegrable_polynomial_sq Q) (fun z => sq_nonneg ‖Q.eval z‖)]
  rw [← ENNReal.ofReal_mul (weightedCircleConstant_nonneg k (2 * k) p hp2 hp3)]
  exact ENNReal.ofReal_le_ofReal (circleAverage_weightedAngular_le Q k (2 * k) p hd hp2 hp3)

/-- The Gaussian pair weighted moment is controlled by the polynomial `L²` mass, by the circle
estimate and Tonelli (no finiteness of the left side is assumed). -/
theorem lintegral_pairWeighted_le (P : MvPolynomial ι ℝ) (k : ℕ) (p : ℝ)
    (hP : P.totalDegree ≤ k) (hp2 : 2 ≤ p) (hp3 : p < 3) :
    (∫⁻ q, pairWeighted P p q
      ∂(stdGaussian (EuclideanSpace ℝ ι)).prod (stdGaussian (EuclideanSpace ℝ ι))) ≤
      ENNReal.ofReal (weightedCircleConstant k (2 * k) p) *
        (∫⁻ x : EuclideanSpace ℝ ι, ENNReal.ofReal (polynomialValue P x ^ 2)
          ∂stdGaussian (EuclideanSpace ℝ ι)) := by
  rw [← lintegral_pair_rotation_average (pairWeighted P p) (measurable_pairWeighted P p)]
  have hcomp : Measurable (fun q : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
      ∫⁻ θ : ℝ, pairSquare P (ContinuousLinearMap.rotation θ q) ∂normalizedCircleAngles) := by
    apply Measurable.lintegral_prod_right
    apply (measurable_pairSquare P).comp
    simp only [ContinuousLinearMap.rotation_apply]
    fun_prop
  calc
    _ ≤ ∫⁻ q, ENNReal.ofReal (weightedCircleConstant k (2 * k) p) *
        (∫⁻ θ : ℝ, pairSquare P (ContinuousLinearMap.rotation θ q) ∂normalizedCircleAngles)
          ∂(stdGaussian (EuclideanSpace ℝ ι)).prod (stdGaussian (EuclideanSpace ℝ ι)) :=
      lintegral_mono (pair_circle_estimate P k p hP hp2 hp3)
    _ = ENNReal.ofReal (weightedCircleConstant k (2 * k) p) *
        ∫⁻ q, pairSquare P q
          ∂(stdGaussian (EuclideanSpace ℝ ι)).prod (stdGaussian (EuclideanSpace ℝ ι)) := by
      rw [lintegral_const_mul _ hcomp, lintegral_pair_rotation_average (pairSquare P) (measurable_pairSquare P)]
    _ = _ := by
      rw [lintegral_prod _ (measurable_pairSquare P).aemeasurable]
      simp [pairSquare]

/-- The weighted-gradient integrand `|∇P|^p |P|^{2-p}`. -/
def gradientWeighted (P : MvPolynomial ι ℝ) (p : ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  ‖euclideanPolynomialGradient P x‖ ^ p * ‖polynomialValue P x‖ ^ (2 - p)

omit [DecidableEq ι] in
/-- The weighted-gradient integrand is measurable. -/
theorem measurable_gradientWeighted (P : MvPolynomial ι ℝ) (p : ℝ) :
    Measurable (gradientWeighted P p) :=
  (((continuous_euclideanPolynomialGradient P).norm.measurable).pow_const p).mul
    (((continuous_polynomialValue P).norm.measurable).pow_const (2 - p))

omit [DecidableEq ι] in
/-- The weighted-gradient integrand is nonnegative. -/
theorem gradientWeighted_nonneg (P : MvPolynomial ι ℝ) (p : ℝ) (x : EuclideanSpace ℝ ι) :
    0 ≤ gradientWeighted P p x :=
  mul_nonneg (Real.rpow_nonneg (norm_nonneg _) p) (Real.rpow_nonneg (norm_nonneg _) (2 - p))

omit [DecidableEq ι] in
/-- The pair weighted moment equals the normal moment times the weighted-gradient integral, by the
directional normal law and Tonelli. -/
theorem lintegral_pairWeighted_eq_normal (P : MvPolynomial ι ℝ) (p : ℝ) :
    (∫⁻ q, pairWeighted P p q
      ∂(stdGaussian (EuclideanSpace ℝ ι)).prod (stdGaussian (EuclideanSpace ℝ ι))) =
      normalEMoment p * (∫⁻ x : EuclideanSpace ℝ ι, ENNReal.ofReal (gradientWeighted P p x)
        ∂stdGaussian (EuclideanSpace ℝ ι)) := by
  let w : EuclideanSpace ℝ ι → ℝ≥0∞ := fun x => ENNReal.ofReal (‖polynomialValue P x‖ ^ (2 - p))
  have hw : Measurable w := ENNReal.measurable_ofReal.comp
    ((continuous_polynomialValue P).norm.measurable.pow_const (2 - p))
  have he : pairWeighted P p = fun q : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
      w q.1 * ENNReal.ofReal (‖⟪euclideanPolynomialGradient P q.1, q.2⟫_ℝ‖ ^ p) := by
    funext q
    unfold pairWeighted w
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) p)]
    exact mul_comm _ _
  rw [he, lintegral_weighted_directional (euclideanPolynomialGradient P)
    (continuous_euclideanPolynomialGradient P).measurable w hw p]
  congr 1
  apply lintegral_congr
  intro x
  unfold gradientWeighted w
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) p)]
  exact mul_comm _ _

/-- The constant of the Gaussian estimate, depending only on the degree `k` and the exponent `p`. -/
def gaussianGradientConstant (k : ℕ) (p : ℝ) : ℝ :=
  weightedCircleConstant k (2 * k) p / normalMoment p

omit [Fintype ι] [DecidableEq ι] in
/-- The constant is nonnegative. -/
theorem gaussianGradientConstant_nonneg (k : ℕ) (p : ℝ) (hp2 : 2 ≤ p) (hp3 : p < 3) :
    0 ≤ gaussianGradientConstant k p :=
  div_nonneg (weightedCircleConstant_nonneg k (2 * k) p hp2 hp3)
    (normalMoment_pos p (by linarith)).le

/-- The weighted-gradient integral estimate in `ℝ≥0∞`, after cancelling the positive finite normal
moment. The constants depend only on `k, p`. -/
theorem lintegral_gradientWeighted_le (P : MvPolynomial ι ℝ) (k : ℕ) (p : ℝ)
    (hP : P.totalDegree ≤ k) (hp2 : 2 ≤ p) (hp3 : p < 3) :
    (∫⁻ x : EuclideanSpace ℝ ι, ENNReal.ofReal (gradientWeighted P p x)
      ∂stdGaussian (EuclideanSpace ℝ ι)) ≤
      ENNReal.ofReal (gaussianGradientConstant k p) *
        (∫⁻ x : EuclideanSpace ℝ ι, ENNReal.ofReal (polynomialValue P x ^ 2)
          ∂stdGaussian (EuclideanSpace ℝ ι)) := by
  have hb := lintegral_pairWeighted_le P k p hP hp2 hp3
  rw [lintegral_pairWeighted_eq_normal, normalEMoment_eq_ofReal p (by linarith)] at hb
  have hnormal := normalMoment_pos p (by linarith : 0 ≤ p)
  have hzero : ENNReal.ofReal (normalMoment p) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hnormal)
  have hc := (ENNReal.mul_le_iff_le_inv hzero ENNReal.ofReal_ne_top).mp hb
  convert hc using 1
  unfold gaussianGradientConstant
  rw [ENNReal.ofReal_div_of_pos hnormal, div_eq_mul_inv]
  ring

/-- The weighted-gradient integrand is integrable, from its integral bound. -/
theorem integrable_gradientWeighted (P : MvPolynomial ι ℝ) (k : ℕ) (p : ℝ)
    (hP : P.totalDegree ≤ k) (hp2 : 2 ≤ p) (hp3 : p < 3) :
    Integrable (gradientWeighted P p) (stdGaussian (EuclideanSpace ℝ ι)) := by
  have hnon : 0 ≤ᵐ[stdGaussian (EuclideanSpace ℝ ι)] gradientWeighted P p :=
    Filter.Eventually.of_forall (gradientWeighted_nonneg P p)
  have hbound := lintegral_gradientWeighted_le P k p hP hp2 hp3
  have hsq := (ofReal_integral_eq_lintegral_ofReal (integrable_polynomialValue_sq P)
    (Filter.Eventually.of_forall (fun x => sq_nonneg (polynomialValue P x)))).symm
  rw [hsq] at hbound
  refine ⟨(measurable_gradientWeighted P p).aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal hnon).mpr
  exact lt_of_le_of_lt hbound (ENNReal.mul_lt_top (by finiteness) (by finiteness))

/-- **Weighted gradient bound for Gaussian polynomials.** For every nonzero real polynomial `P` of total degree
at most `k` and every `2 ≤ p < 3`, the singular weighted gradient `gradientWeighted P p` is integrable under the
standard Gaussian measure, with integral at most `gaussianGradientConstant k p` times the Gaussian `L²` mass of `P`.
The constant depends only on `k` and `p`. -/
theorem gaussian_polynomial_gradient (P : MvPolynomial ι ℝ) (k : ℕ) (p : ℝ)
    (_hP0 : P ≠ 0) (hP : P.totalDegree ≤ k) (hp2 : 2 ≤ p) (hp3 : p < 3) :
    Integrable (gradientWeighted P p) (stdGaussian (EuclideanSpace ℝ ι)) ∧
      (∫ x : EuclideanSpace ℝ ι, gradientWeighted P p x ∂stdGaussian (EuclideanSpace ℝ ι)) ≤
        gaussianGradientConstant k p *
          (∫ x : EuclideanSpace ℝ ι, polynomialValue P x ^ 2 ∂stdGaussian (EuclideanSpace ℝ ι)) := by
  have hf := integrable_gradientWeighted P k p hP hp2 hp3
  refine ⟨hf, ?_⟩
  have hb := lintegral_gradientWeighted_le P k p hP hp2 hp3
  rw [← ofReal_integral_eq_lintegral_ofReal hf
      (Filter.Eventually.of_forall (gradientWeighted_nonneg P p)),
    ← ofReal_integral_eq_lintegral_ofReal (integrable_polynomialValue_sq P)
      (Filter.Eventually.of_forall (fun x => sq_nonneg (polynomialValue P x))),
    ← ENNReal.ofReal_mul (gaussianGradientConstant_nonneg k p hp2 hp3)] at hb
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (gaussianGradientConstant_nonneg k p hp2 hp3)
    (integral_nonneg (fun x => sq_nonneg (polynomialValue P x))))).mp hb

omit [Fintype ι] [DecidableEq ι] in
/-- **The Gaussian polynomial gradient estimate.** `C` is chosen before the finite index type and
the nonzero real polynomial: for all `2 ≤ p < 3` and degree at most `k`,
`E |∇P|^p |P|^{2-p} ≤ C E P²` under `stdGaussian`. -/
theorem exists_gaussian_polynomial_gradient_constant (k : ℕ) (p : ℝ)
    (hp2 : 2 ≤ p) (hp3 : p < 3) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : Type u) [Fintype J] (P : MvPolynomial J ℝ),
      P ≠ 0 → P.totalDegree ≤ k →
        Integrable (gradientWeighted P p) (stdGaussian (EuclideanSpace ℝ J)) ∧
          (∫ x : EuclideanSpace ℝ J, gradientWeighted P p x ∂stdGaussian (EuclideanSpace ℝ J)) ≤
            C * (∫ x : EuclideanSpace ℝ J, polynomialValue P x ^ 2 ∂stdGaussian (EuclideanSpace ℝ J)) := by
  classical
  refine ⟨1 + gaussianGradientConstant k p, by
    have hc := gaussianGradientConstant_nonneg k p hp2 hp3
    linarith, ?_⟩
  intro J hJ P hP0 hP
  have h := gaussian_polynomial_gradient P k p hP0 hP hp2 hp3
  refine ⟨h.1, h.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (by linarith)
    (integral_nonneg (fun x => sq_nonneg (polynomialValue P x)))

end BlockBand.DeterminantScore.GaussianGradient
