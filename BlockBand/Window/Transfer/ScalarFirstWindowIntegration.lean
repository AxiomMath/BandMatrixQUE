module

public import BlockBand.Window.Transfer.CorrelatedWindowLocalization
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.HasLaw
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Integrating the scalar Gaussian first

For a probability space `(Ω, μ, Y, t)` with `t ~ N(0,σ²)` independent of `Y`, Fubini
integrates the scalar first: `E[A(Y) w(scale(X(Y)+t-E))] = E[A(Y) h(X(Y))]`, with integrability;
and capped and localized versions. `A` and `X` may be arbitrarily correlated.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

open MeasureTheory ProbabilityTheory

namespace BlockBand.Window.Transfer

variable {Omega State : Type*} [MeasurableSpace Omega] [MeasurableSpace State]

/-- Integrability of `A(y) w(scale(X(y) + t - E))` under the product law, uniformly in `X` and
`σ`, from the compact support of `w` and `0 ≤ A ≤ 1`. -/
theorem integrable_scalar_window_product (nu : Measure State) [IsProbabilityMeasure nu]
    (A X : State → ℝ) (hA : Measurable A) (hX : Measurable X)
    (hA0 : ∀ y, 0 ≤ A y) (hA1 : ∀ y, A y ≤ 1)
    (w : ℝ → ℝ) (hw : Continuous w) (hcompact : HasCompactSupport w)
    (scale E sigma : ℝ) :
    Integrable (fun z : State × ℝ =>
      A z.1 * w (scale * (X z.1 + z.2 - E)))
      (nu.prod (gaussianReal 0 (scalarVariance sigma))) := by
  obtain ⟨C, hC⟩ := hw.bounded_above_of_compact_support hcompact
  have hm : Measurable (fun z : State × ℝ =>
      A z.1 * w (scale * (X z.1 + z.2 - E))) :=
    (hA.comp measurable_fst).mul (hw.measurable.comp
      ((((hX.comp measurable_fst).add measurable_snd).sub_const E).const_mul scale))
  apply (integrable_const C).mono' hm.aestronglyMeasurable
  filter_upwards with z
  rw [norm_mul]
  have hAnorm : ‖A z.1‖ ≤ 1 := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hA0 z.1)] using hA1 z.1
  exact (mul_le_of_le_one_left (norm_nonneg _) hAnorm).trans (hC _)

/-- **Scalar-first window integration.** If `t ~ N(0,σ²)` is independent of `Y`, then
`E[A(Y)w(scale(X(Y)+t−E))] = E[A(Y)h(X(Y))]` with integrability, `h = scalarConvolution w scale E σ`;
`A` and `X` may be correlated.
-/
theorem scalar_first_window_integral (mu : Measure Omega) [IsProbabilityMeasure mu]
    (Y : Omega → State) (t : Omega → ℝ) (hY : Measurable Y) (ht : Measurable t)
    (sigma : ℝ) (hlaw : HasLaw t (gaussianReal 0 (scalarVariance sigma)) mu)
    (hind : IndepFun Y t mu)
    (A X : State → ℝ) (hA : Measurable A) (hX : Measurable X)
    (hA0 : ∀ y, 0 ≤ A y) (hA1 : ∀ y, A y ≤ 1)
    (w : ℝ → ℝ) (hw : Continuous w) (hcompact : HasCompactSupport w)
    (scale E : ℝ) :
    Integrable (fun omega =>
      A (Y omega) * w (scale * (X (Y omega) + t omega - E))) mu ∧
    Integrable (fun y => A y * scalarConvolution w scale E sigma (X y)) (mu.map Y) ∧
    (∫ omega, A (Y omega) * w (scale * (X (Y omega) + t omega - E)) ∂mu) =
      ∫ y, A y * scalarConvolution w scale E sigma (X y) ∂(mu.map Y) := by
  let nu : Measure State := mu.map Y
  let : IsProbabilityMeasure nu :=
    (Measure.isProbabilityMeasure_map_iff hY.aemeasurable).mpr inferInstance
  let gamma : Measure ℝ := gaussianReal 0 (scalarVariance sigma)
  let F : State × ℝ → ℝ := fun z => A z.1 * w (scale * (X z.1 + z.2 - E))
  have hPair : Measurable (fun omega => (Y omega, t omega)) := hY.prodMk ht
  have hFm : Measurable F :=
    (hA.comp measurable_fst).mul (hw.measurable.comp
      ((((hX.comp measurable_fst).add measurable_snd).sub_const E).const_mul scale))
  have hJoint : mu.map (fun omega => (Y omega, t omega)) = nu.prod gamma := by
    rw [hind.map_prod_eq_prod_map_map hY.aemeasurable ht.aemeasurable, hlaw.map_eq]
  have hProd : Integrable F (nu.prod gamma) :=
    integrable_scalar_window_product nu A X hA hX hA0 hA1 w hw hcompact scale E sigma
  have hMap : Integrable F (mu.map (fun omega => (Y omega, t omega))) := by
    rw [hJoint]
    exact hProd
  have hOriginal : Integrable (fun omega => F (Y omega, t omega)) mu :=
    (integrable_map_measure hFm.aestronglyMeasurable hPair.aemeasurable).mp hMap
  have hInner : (fun y => ∫ s, F (y,s) ∂gamma) =
      (fun y => A y * scalarConvolution w scale E sigma (X y)) := by
    funext y
    dsimp only [F, gamma, scalarConvolution]
    exact integral_const_mul _ _
  have hMarginal := hProd.integral_prod_left
  rw [hInner] at hMarginal
  refine ⟨hOriginal, hMarginal, ?_⟩
  change (∫ omega, F (Y omega, t omega) ∂mu) = _
  calc
    _ = ∫ z, F z ∂(mu.map (fun omega => (Y omega, t omega))) :=
      (integral_map hPair.aemeasurable hFm.aestronglyMeasurable).symm
    _ = ∫ z, F z ∂(nu.prod gamma) := by rw [hJoint]
    _ = ∫ y, A y * scalarConvolution w scale E sigma (X y) ∂nu := by
      rw [integral_prod F hProd, hInner]

/-- Gaussian-window localization with an arbitrarily correlated observable. The terminal `L^q`
moment is taken under the marginal law of `Y` and the observable mean bound under the full law.
The large-distance condition is the classical separation exceeding the window width; small
ranks, the rank sum and the critical remainder are treated separately. -/
theorem scalar_first_correlated_window_localization
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (Y : Omega → State) (t : Omega → ℝ) (hY : Measurable Y) (ht : Measurable t)
    (sigma : ℝ) (hlaw : HasLaw t (gaussianReal 0 (scalarVariance sigma)) mu)
    (hind : IndepFun Y t mu)
    (A X : State → ℝ) (hA : Measurable A) (hX : Measurable X)
    (hA0 : ∀ y, 0 ≤ A y) (hA1 : ∀ y, A y ≤ 1)
    (w : ℝ → ℝ) (hw : Continuous w) (hcompact : HasCompactSupport w)
    (hunit : ∫ x, w x = 1) (hw0 : ∀ x, 0 ≤ w x)
    (scale E M e q L epsilon : ℝ) (hs : 0 < scale) (hsigma : 0 < sigma)
    (hq : 0 < q) (hL : 0 ≤ L) (hsupp : ∀ x, w x ≠ 0 → |x| ≤ M)
    (hg : 0 < |e - E|) (hwidth : 4 * (M / scale) ≤ |e - E|)
    (hLp : eLpNorm (fun y => X y - e) (ENNReal.ofReal q) (mu.map Y) ≤
      ENNReal.ofReal L)
    (hepsilon : (∫ omega, A (Y omega) ∂mu) ≤ epsilon) :
    Integrable (fun omega =>
      A (Y omega) * w (scale * (X (Y omega) + t omega - E))) mu ∧
    (∫ omega, A (Y omega) * w (scale * (X (Y omega) + t omega - E)) ∂mu) ≤
      scalarKernelPrefactor scale sigma *
        min epsilon ((2 / |e - E|) ^ q * L ^ q +
          Real.exp (-|e - E| ^ 2 / (32 * sigma ^ 2))) := by
  let : IsProbabilityMeasure (mu.map Y) :=
    (Measure.isProbabilityMeasure_map_iff hY.aemeasurable).mpr inferInstance
  have hLift : (∫ y, A y ∂(mu.map Y)) ≤ epsilon := by
    rw [integral_map hY.aemeasurable hA.aestronglyMeasurable]
    exact hepsilon
  have hIdentity := scalar_first_window_integral mu Y t hY ht sigma hlaw hind
    A X hA hX hA0 hA1 w hw hcompact scale E
  have hLocalization := correlated_expectation_localization
    (mu.map Y) A X hA hX hA0 hA1 w hw hcompact hunit hw0
    scale E sigma M e q L epsilon hs hsigma hq hL hsupp hg hwidth hLp hLift
  refine ⟨hIdentity.1, ?_⟩
  rw [hIdentity.2.2]
  exact hLocalization.2

/-- The window expectation is at most `B ε`, with integrability and without any energy separation
or moment condition. This treats the small-rank region of the physical rank sum. -/
theorem scalar_first_window_expectation_cap
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (Y : Omega → State) (t : Omega → ℝ) (hY : Measurable Y) (ht : Measurable t)
    (sigma : ℝ) (hlaw : HasLaw t (gaussianReal 0 (scalarVariance sigma)) mu)
    (hind : IndepFun Y t mu)
    (A X : State → ℝ) (hA : Measurable A) (hX : Measurable X)
    (hA0 : ∀ y, 0 ≤ A y) (hA1 : ∀ y, A y ≤ 1)
    (w : ℝ → ℝ) (hw : Continuous w) (hcompact : HasCompactSupport w)
    (hunit : ∫ x, w x = 1) (hw0 : ∀ x, 0 ≤ w x)
    (scale E M epsilon : ℝ) (hs : 0 < scale) (hsigma : 0 < sigma)
    (hsupp : ∀ x, w x ≠ 0 → |x| ≤ M)
    (hepsilon : (∫ omega, A (Y omega) ∂mu) ≤ epsilon) :
    Integrable (fun omega =>
      A (Y omega) * w (scale * (X (Y omega) + t omega - E))) mu ∧
    (∫ omega, A (Y omega) * w (scale * (X (Y omega) + t omega - E)) ∂mu) ≤
      scalarKernelPrefactor scale sigma * epsilon := by
  let : IsProbabilityMeasure (mu.map Y) :=
    (Measure.isProbabilityMeasure_map_iff hY.aemeasurable).mpr inferInstance
  let B := scalarKernelPrefactor scale sigma
  have hB : 0 ≤ B := by unfold B scalarKernelPrefactor; positivity
  have hIdentity := scalar_first_window_integral mu Y t hY ht sigma hlaw hind
    A X hA hX hA0 hA1 w hw hcompact scale E
  have hAi : Integrable A (mu.map Y) :=
    (integrable_const (1 : ℝ)).mono' hA.aestronglyMeasurable (ae_of_all _ fun y => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hA0 y)] using hA1 y)
  have hLift : (∫ y, A y ∂(mu.map Y)) ≤ epsilon := by
    rw [integral_map hY.aemeasurable hA.aestronglyMeasurable]
    exact hepsilon
  refine ⟨hIdentity.1, ?_⟩
  calc
    _ = ∫ y, A y * scalarConvolution w scale E sigma (X y) ∂(mu.map Y) := hIdentity.2.2
    _ ≤ ∫ y, B * A y ∂(mu.map Y) :=
      integral_mono hIdentity.2.1 (hAi.const_mul B) fun y => by
        have hk := (scalarConvolution_uniform w hw hcompact hunit hw0
          scale E sigma M (X y) hs hsigma hsupp).2
        simpa only [mul_comm B] using mul_le_mul_of_nonneg_left hk (hA0 y)
    _ = B * ∫ y, A y ∂(mu.map Y) := integral_const_mul _ _
    _ ≤ B * epsilon := mul_le_mul_of_nonneg_left hLift hB

end BlockBand.Window.Transfer
