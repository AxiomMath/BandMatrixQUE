module
public import BlockBand.GaussianBulk.LevelVerticalAction
public import Mathlib.MeasureTheory.Integral.Gamma

/-!
# Gaussian integrals along the vertical saddle line

The exponential `relativeVerticalExp` of the vertical phase difference along `Re z = x` has an
almost-everywhere Gaussian majorant with a coefficient depending only on `η` and `tmax`, hence is
Lebesgue integrable with an explicit tail bound. The planar majorant `gaussianCrossingMajorant`
of the transverse saddle singularity has the explicit integral `π^(3/2)/√(c n)`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.GaussianBulk
open MeasureTheory Filter Set
open scoped BigOperators

/-- The dimension-free constant in the vertical Gaussian action bound. -/
def verticalTailConstant (η tmax : ℝ) : ℝ :=
  Real.log (2*tmax/η^2)/2+η^2/(4*tmax)

/-- The exponential of `n` times the vertical phase difference `S(x+iv) - S(x+iy)`. -/
def relativeVerticalExp {N : ℕ} (d : Fin N → ℝ)
    (E t x y n v : ℝ) : ℂ :=
  Complex.exp ((n : ℂ)*(saddlePhase d E t ((x : ℂ)+(v : ℂ)*Complex.I)-
    saddlePhase d E t ((x : ℂ)+(y : ℂ)*Complex.I)))

private theorem vertical_safe_of_ne_zero {N : ℕ} (d : Fin N → ℝ)
    (x v : ℝ) (hv : v ≠ 0) : VerticalActionDomain d x v := by
  intro j
  have hs := sq_pos_of_ne_zero hv
  nlinarith [sq_nonneg (x-d j)]

/-- The modulus of `relativeVerticalExp` in terms of the real vertical action; in applications
`n = N` is the Johansson exponent. -/
theorem norm_relativeVerticalExp {N : ℕ} (d : Fin N → ℝ)
    (E t x y n v : ℝ) : ‖relativeVerticalExp d E t x y n v‖ =
      Real.exp (n*(verticalRealAction d E t x v-verticalRealAction d E t x y)) := by
  rw [relativeVerticalExp,Complex.norm_exp]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    Complex.sub_re,← verticalRealAction_eq_saddlePhase_re]

/-- A positive level root gives a global almost-everywhere Gaussian majorant of the real vertical
action. The only possible real pole is `v = 0`, a Lebesgue null set. The coefficient depends
only on `η` and `tmax`, not on `N` or `d`. -/
theorem verticalRealAction_global_gaussian_ae {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (E t x y η tmax : ℝ) (ht : 0 < t)
    (hr : PositiveLevelRoot d t x y) (hη : 0 < η) (hheight : η ≤ y)
    (htmax : t ≤ tmax) :
    ∀ᵐ v : ℝ, verticalRealAction d E t x v-verticalRealAction d E t x y ≤
      -v^2/(4*tmax)+|verticalTailConstant η tmax|+1 := by
  have htM : 0 < tmax := lt_of_lt_of_le ht htmax
  have he := levelHeight_eq_of_root hN d t x y ht hr
  have hy2 : y^2 ≤ tmax := by
    have hb := positiveLevelRoot_le_sqrt hN d t x y ht hr
    nlinarith [Real.sq_sqrt ht.le,Real.sqrt_nonneg t]
  filter_upwards [volume.ae_ne (0 : ℝ)] with v hv
  have hd := vertical_safe_of_ne_zero d x v hv
  by_cases htail : y^2 ≤ v^2
  · have hb := verticalRealAction_gaussian_tail hN d E t x y v η tmax ht hr
      hη hheight htmax htail
    have hC := le_abs_self (verticalTailConstant η tmax)
    unfold verticalTailConstant at hC ⊢
    linarith
  · have hm := verticalRealAction_max hN d E t x v ht hd
    rw [he] at hm
    have hq : v^2/(4*tmax) ≤ 1 := by
      apply (div_le_iff₀ (by positivity : 0 < 4*tmax)).mpr
      linarith [not_le.mp htail]
    have heq : -v^2/(4*tmax)= -(v^2/(4*tmax)) := by ring
    rw [heq]
    linarith [abs_nonneg (verticalTailConstant η tmax)]

/-- Lebesgue integrability of the vertical phase exponential on the whole real line, the finite
poles being removed almost everywhere. -/
theorem integrable_relativeVerticalExp {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (E t x y η tmax n : ℝ) (ht : 0 < t)
    (hr : PositiveLevelRoot d t x y) (hη : 0 < η) (hheight : η ≤ y)
    (htmax : t ≤ tmax) (hn : 0 < n) :
    Integrable (relativeVerticalExp d E t x y n) := by
  have htM : 0 < tmax := lt_of_lt_of_le ht htmax
  let C := |verticalTailConstant η tmax|+1
  have hg : Integrable (fun v : ℝ => Real.exp (n*C)*Real.exp (-(n/(4*tmax))*v^2)) :=
    (integrable_exp_neg_mul_sq (by positivity : 0 < n/(4*tmax))).const_mul _
  apply hg.mono'
  · unfold relativeVerticalExp saddlePhase complexMean
    fun_prop
  · filter_upwards [verticalRealAction_global_gaussian_ae hN d E t x y η tmax ht hr
      hη hheight htmax] with v hv
    rw [norm_relativeVerticalExp,← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have he : n*C+ -(n/(4*tmax))*v^2 = n*(-v^2/(4*tmax)+C) := by ring
    rw [he]
    have hv' : verticalRealAction d E t x v-verticalRealAction d E t x y ≤
        -v^2/(4*tmax)+C := by dsimp only [C]; linarith
    exact mul_le_mul_of_nonneg_left hv' hn.le

/-- Quantitative vertical tail integral: for a cutoff `R` with `R² ≥ y²`, the tail is at most
`exp(n·verticalTailConstant - n R²/(8 tmax)) · √(8π tmax/n)`, with a constant independent of `N` and `d` apart from the exponent
`n = N`. -/
theorem integral_relativeVerticalExp_tail_le {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (E t x y η tmax n R : ℝ) (ht : 0 < t)
    (hr : PositiveLevelRoot d t x y) (hη : 0 < η) (hheight : η ≤ y)
    (htmax : t ≤ tmax) (hn : 0 < n) (hR : y^2 ≤ R^2) :
    (∫ v in {v : ℝ | R^2 ≤ v^2}, ‖relativeVerticalExp d E t x y n v‖) ≤
      Real.exp (n*verticalTailConstant η tmax-n*R^2/(8*tmax))*
        Real.sqrt (Real.pi/(n/(8*tmax))) := by
  have htM : 0 < tmax := lt_of_lt_of_le ht htmax
  let S : Set ℝ := {v | R^2 ≤ v^2}
  have hS : MeasurableSet S := (isClosed_le continuous_const (continuous_id.pow 2)).measurableSet
  let C := Real.exp (n*verticalTailConstant η tmax-n*R^2/(8*tmax))
  let g : ℝ → ℝ := fun v => C*Real.exp (-(n/(8*tmax))*v^2)
  have hg : Integrable g :=
    (integrable_exp_neg_mul_sq (by positivity : 0 < n/(8*tmax))).const_mul C
  have hf := (integrable_relativeVerticalExp hN d E t x y η tmax n ht hr hη hheight htmax hn).norm
  have hbound : ∀ᵐ v ∂volume.restrict S, ‖relativeVerticalExp d E t x y n v‖ ≤ g v := by
    filter_upwards [ae_restrict_mem hS] with v hv
    have hvy : y^2 ≤ v^2 := le_trans hR hv
    have hd : VerticalActionDomain d x v := by
      intro j
      have hp := sq_pos_of_pos hr.1
      nlinarith [sq_nonneg (x-d j)]
    have hb := verticalRealAction_gaussian_tail hN d E t x y v η tmax ht hr hη hheight htmax hvy
    rw [norm_relativeVerticalExp]
    dsimp only [g,C]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hnB := mul_le_mul_of_nonneg_left hb hn.le
    have hcut := mul_le_mul_of_nonneg_left hv
      (show 0 ≤ n/(8*tmax) by positivity)
    change R^2 ≤ v^2 at hv
    have he : n*(-v^2/(4*tmax)+Real.log (2*tmax/η^2)/2+η^2/(4*tmax)) =
      n*verticalTailConstant η tmax-2*(n/(8*tmax))*v^2 := by
      unfold verticalTailConstant
      ring
    rw [he] at hnB
    have he2 : n*R^2/(8*tmax)=(n/(8*tmax))*R^2 := by ring
    rw [he2]
    linarith
  have hm := integral_mono_ae hf.integrableOn hg.integrableOn hbound
  have hwhole : (∫ v in S, g v) ≤ ∫ v, g v :=
    integral_mono_measure Measure.restrict_le_self (by filter_upwards with v; dsimp [g,C]; positivity) hg
  have he : (∫ v, g v) = C*Real.sqrt (Real.pi/(n/(8*tmax))) := by
    rw [show g=(fun v => C*Real.exp (-(n/(8*tmax))*v^2)) from rfl,
      integral_const_mul,integral_gaussian]
  exact le_trans hm (he ▸ hwhole)

/-- Planar majorant for the transverse saddle singularity of the remainder integrand. The value
at `z = 0` is set to zero; this singleton is Lebesgue null. -/
def gaussianCrossingMajorant (c n : ℝ) (z : ℂ) : ℝ :=
  Real.exp (-c*n*‖z‖^2)/‖z‖

/-- The polar Gaussian singular integral equals `π^(3/2)/√(c n)`, which gives the `n^{-1/2}` scale. -/
theorem integral_gaussianCrossingMajorant (c n : ℝ) (hc : 0 < c) (hn : 0 < n) :
    (∫ z : ℂ, gaussianCrossingMajorant c n z) =
      Real.pi*Real.sqrt Real.pi/Real.sqrt (c*n) := by
  have h := Complex.integral_rpow_mul_exp_neg_mul_rpow
    (p := 2) (q := -1) (b := c*n) (by norm_num) (by norm_num) (mul_pos hc hn)
  have hp : (c*n)^(-(1/2 : ℝ))=(Real.sqrt (c*n))⁻¹ := by
    rw [Real.rpow_neg (mul_pos hc hn).le,← Real.sqrt_eq_rpow]
  norm_num only at h
  rw [hp,Real.Gamma_one_half_eq] at h
  have hpi : 2*Real.pi/2=Real.pi := by ring
  rw [hpi] at h
  have hfun : gaussianCrossingMajorant c n =
      (fun z : ℂ => ‖z‖^(-1 : ℝ)*Real.exp (-(c*n)*‖z‖^(2 : ℝ))) := by
    funext z
    simp only [gaussianCrossingMajorant,Real.rpow_neg_one,Real.rpow_two]
    rw [show -c*n*‖z‖^2= -(c*n)*‖z‖^2 by ring,div_eq_mul_inv,mul_comm]
  rw [hfun,h]
  ring

/-- Integrability of the crossing Gaussian majorant, including at the origin. -/
theorem integrable_gaussianCrossingMajorant (c n : ℝ) (hc : 0 < c) (hn : 0 < n) :
    Integrable (gaussianCrossingMajorant c n) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_gaussianCrossingMajorant c n hc hn]
  exact ne_of_gt (by positivity)

/-- The integral of the crossing majorant over any set is at most `π^(3/2)/√(c n)`. -/
theorem integral_gaussianCrossingMajorant_restrict_le (c n : ℝ) (hc : 0 < c)
    (hn : 0 < n) (S : Set ℂ) :
    (∫ z in S, gaussianCrossingMajorant c n z) ≤
      Real.pi*Real.sqrt Real.pi/Real.sqrt (c*n) := by
  rw [← integral_gaussianCrossingMajorant c n hc hn]
  exact integral_mono_measure Measure.restrict_le_self
    (by filter_upwards with z; unfold gaussianCrossingMajorant; positivity)
    (integrable_gaussianCrossingMajorant c n hc hn)

end BlockBand.GaussianBulk
