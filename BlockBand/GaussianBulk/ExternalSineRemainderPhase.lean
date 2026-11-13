module

public import BlockBand.GaussianBulk.ExternalSineRemainderPath
public import BlockBand.GaussianBulk.NativeKernelPhaseAdapter

/-!
# The gauged remainder integrand and its majorant

Deterministic. Domain: `N > 0`, `t > 0`, `ρ > 0`, an arbitrary real (possibly repeated) source `d`,
`S = t/N`, `u = E + ξ/(Nρ)`, `v = E + ζ/(Nρ)`, the vertical line `Γ = x₀ + iℝ`;
`G = gaugedJohanssonExp d E t ρ x₀ ξ ζ`, and `remainderGauge` is the real gauge factor
`exp(β - g(ξ) + g(ζ))`.

Pointwise majorant of the gauged remainder integrand by a vertical integral, and the uniform
bound on its vertical mass.

* `norm_gaugedJohanssonExp_vertical`: for every `z` (not only graph points), `‖G(z, x₀+iv)‖ =
  exp(N(Re S(x₀+iv) - Re S(z)) + ξ(Re z - x₀)/(tρ))`;
* `norm_gauge_mul_remainderIntegrand_le`: off `Re z = x₀` and the poles,
  `‖gauge · W(z)‖ ≤ remainderMajorant z := ∫_v ‖G(z,x₀+iv)‖/‖x₀+iv-z‖` (`W` the
  remainder integrand of the residue representation; no integrability is needed for this inequality);
* `remainderMajorant_star`: `remainderMajorant (conj z) = remainderMajorant z`;
* `integral_norm_relativeVerticalExp_le`: `∫_ℝ ‖relativeVerticalExp_n‖ ≤ verticalMassConstant η tmax`
  for every `n ≥ 1`, uniformly in `d` (from the global maxima at `±y₀` and the Gaussian tail).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.GaussianBulk

open Set MeasureTheory Filter Topology
open BlockBand.External
open scoped NNReal

/-- The real gauge factor `exp(β - g(ξ) + g(ζ))` of the normalized kernel,
`β = N(v² - u²)/(2t)`, `g = realSineGauge N E t ρ x₀`. -/
def remainderGauge (N : ℕ) (E t rho x₀ xi zeta : ℝ) : ℂ :=
  Complex.exp (((N:ℝ)*((E+zeta/((N:ℝ)*rho))^2-(E+xi/((N:ℝ)*rho))^2)/(2*t)-
    realSineGauge N E t rho x₀ xi+realSineGauge N E t rho x₀ zeta:ℝ):ℂ)

/-- The vertical majorant `∫_v ‖G(z, x₀+iv)‖ / ‖x₀+iv - z‖` of the gauged remainder. -/
def remainderMajorant {N : ℕ} (d : Fin N → ℝ) (E t rho x₀ xi zeta : ℝ) (z : ℂ) : ℝ :=
  ∫ v : ℝ, ‖gaugedJohanssonExp d E t rho x₀ xi zeta z ((x₀:ℂ)+(v:ℂ)*Complex.I)‖ /
    ‖((x₀:ℂ)+(v:ℂ)*Complex.I)-z‖

/-- Norm of the gauged exponential at an arbitrary `z` and a point of `Γ = x₀ + iℝ`. -/
theorem norm_gaugedJohanssonExp_vertical {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E t rho x₀ v xi zeta : ℝ) (ht : 0 < t) (hrho : 0 < rho) (z : ℂ) :
    ‖gaugedJohanssonExp d E t rho x₀ xi zeta z ((x₀:ℂ)+(v:ℂ)*Complex.I)‖ =
      Real.exp ((N:ℝ)*(verticalRealAction d E t x₀ v-verticalRealAction d E t z.re z.im)+
        xi*(z.re-x₀)/(t*rho)) := by
  have hg := microscopic_phase_gauge_identity N hN E t rho x₀ xi zeta ht hrho
  have he : (N:ℝ)*((E+zeta/((N:ℝ)*rho))^2-(E+xi/((N:ℝ)*rho))^2)/(2*t)-
      realSineGauge N E t rho x₀ xi+realSineGauge N E t rho x₀ zeta+
        xi/(t*rho)*z.re-zeta/(t*rho)*x₀=xi*(z.re-x₀)/(t*rho) := by
    linear_combination hg
  have hz : (saddlePhase d E t z).re = verticalRealAction d E t z.re z.im := by
    rw [verticalRealAction_eq_saddlePhase_re, Complex.re_add_im]
  have hw := (verticalRealAction_eq_saddlePhase_re d E t x₀ v).symm
  unfold gaugedJohanssonExp
  rw [Complex.norm_exp]
  simp only [Complex.sub_re,Complex.add_re,Complex.ofReal_re,Complex.mul_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.natCast_im,Complex.natCast_re,
    mul_zero,zero_mul,sub_zero,add_zero]
  rw [hz, hw]
  congr 1
  linear_combination he

/-- Factorization: `‖G(z, x₀+iv)‖ = ‖relativeVerticalExp_N(v)‖ ·
exp(-N(Re S(z) - Re S(x₀+iy)) + ξ(Re z - x₀)/(tρ))`. -/
theorem norm_gaugedJohanssonExp_factor {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E t rho x₀ y v xi zeta : ℝ) (ht : 0 < t) (hrho : 0 < rho) (z : ℂ) :
    ‖gaugedJohanssonExp d E t rho x₀ xi zeta z ((x₀:ℂ)+(v:ℂ)*Complex.I)‖ =
      ‖relativeVerticalExp d E t x₀ y (N:ℝ) v‖ *
        Real.exp (-(N:ℝ)*(verticalRealAction d E t z.re z.im-verticalRealAction d E t x₀ y)+
          xi*(z.re-x₀)/(t*rho)) := by
  rw [norm_gaugedJohanssonExp_vertical hN d E t rho x₀ v xi zeta ht hrho z,
    norm_relativeVerticalExp, ← Real.exp_add]
  congr 1
  ring

/-- **Pointwise majorant of the gauged remainder.** For `z` off `Re z = x₀`, left of `L'`, and
not a pole: `‖gauge · W(z)‖ ≤ remainderMajorant z`, where `W` is the
remainder integrand of the residue representation with `S = t/N`, `u = E + ξ/(Nρ)`, `v = E + ζ/(Nρ)`. -/
theorem norm_gauge_mul_remainderIntegrand_le {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E rho x₀ xi zeta L' : ℝ) (t : ℝ≥0) (ht : 0 < t) (hrho : 0 < rho) (z : ℂ)
    (hz : z.re ≠ x₀) (hzL : z.re < L') (hzd : ∀ j, z ≠ (d j : ℂ)) :
    ‖remainderGauge N E (t:ℝ) rho x₀ xi zeta *
        remainderIntegrand (Johansson.sourceTime N t) d (E+xi/((N:ℝ)*rho))
          (E+zeta/((N:ℝ)*rho)) L' x₀ z‖ ≤
      remainderMajorant d E (t:ℝ) rho x₀ xi zeta z := by
  have hS : 0 < Johansson.sourceTime N t := by
    rw [Johansson.sourceTime]
    exact div_pos ht (by exact_mod_cast hN)
  rw [remainderIntegrand_eq_vertical _ hS d _ _ L' x₀ z hz hzL hzd]
  unfold Johansson.verticalIntegral
  rw [← integral_const_mul]
  have hz' : ∀ j, z-(d j:ℂ) ≠ 0 := fun j => sub_ne_zero.mpr (hzd j)
  have hae : (fun y : ℝ => remainderGauge N E (t:ℝ) rho x₀ xi zeta *
      (Complex.I * Johansson.kernelIntegrand (Johansson.sourceTime N t) d
        (E+xi/((N:ℝ)*rho)) (E+zeta/((N:ℝ)*rho)) z ((x₀:ℂ)+(y:ℂ)*Complex.I))) =ᵐ[volume]
      fun y => Complex.I * (gaugedJohanssonExp d E (t:ℝ) rho x₀ xi zeta z
        ((x₀:ℂ)+(y:ℂ)*Complex.I) / (((x₀:ℂ)+(y:ℂ)*Complex.I)-z)) := by
    have h0 : ({0} : Set ℝ)ᶜ ∈ ae volume := by
      rw [compl_mem_ae_iff]; exact measure_singleton _
    filter_upwards [h0] with y hy
    have hy0 : y ≠ 0 := by simpa using hy
    have hw : ∀ j, ((x₀:ℂ)+(y:ℂ)*Complex.I)-(d j:ℂ) ≠ 0 := by
      intro j h
      have := congrArg Complex.im h
      simp at this
      exact hy0 this
    have h := gaugedNativeKernelIntegrand_eq hN d E rho x₀ xi zeta t ht hrho z
      ((x₀:ℂ)+(y:ℂ)*Complex.I) hz' hw
    simp only at h
    unfold remainderGauge
    rw [← h]
    ring
  rw [integral_congr_ae hae]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  unfold remainderMajorant
  congr 1
  funext y
  rw [norm_mul, Complex.norm_I, one_mul, norm_div]

/-- Conjugation symmetry of the majorant (via `v ↦ -v`). -/
theorem remainderMajorant_star {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E t rho x₀ xi zeta : ℝ) (ht : 0 < t) (hrho : 0 < rho) (z : ℂ) :
    remainderMajorant d E t rho x₀ xi zeta (star z) = remainderMajorant d E t rho x₀ xi zeta z := by
  unfold remainderMajorant
  rw [← integral_neg_eq_self (fun v : ℝ =>
    ‖gaugedJohanssonExp d E t rho x₀ xi zeta z ((x₀:ℂ)+(v:ℂ)*Complex.I)‖ /
      ‖((x₀:ℂ)+(v:ℂ)*Complex.I)-z‖) volume]
  congr 1
  funext v
  rw [norm_gaugedJohanssonExp_vertical hN d E t rho x₀ v xi zeta ht hrho,
    norm_gaugedJohanssonExp_vertical hN d E t rho x₀ (-v) xi zeta ht hrho,
    verticalRealAction_even d E t x₀ v]
  have hre : (star z).re = z.re := by simp
  have him : (star z).im = -z.im := by simp
  rw [hre, him, verticalRealAction_even]
  congr 1
  have hc : star (((x₀:ℂ)+(v:ℂ)*Complex.I)-star z) = ((x₀:ℂ)+((-v:ℝ):ℂ)*Complex.I)-z := by
    apply Complex.ext <;> simp
  rw [← hc, norm_star]

/-- The uniform vertical mass constant: core `2R`, `R² = 8 tmax |T| + tmax`, plus the Gaussian
tail `√(8π tmax)`, `T = verticalTailConstant η tmax`. -/
def verticalMassConstant (η tmax : ℝ) : ℝ :=
  2*Real.sqrt (8*tmax*|verticalTailConstant η tmax|+tmax)+Real.sqrt (8*Real.pi*tmax)

/-- **Vertical mass.** For a positive level root `y ≥ η` at `x`, `0 < t ≤ tmax` and every
`n ≥ 1`: `∫_ℝ ‖relativeVerticalExp d E t x y n v‖ dv ≤ verticalMassConstant η tmax`, uniformly
in `d`. -/
theorem integral_norm_relativeVerticalExp_le {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E t x y η tmax n : ℝ) (ht : 0 < t) (hr : PositiveLevelRoot d t x y) (hη : 0 < η)
    (hheight : η ≤ y) (htmax : t ≤ tmax) (hn : 1 ≤ n) :
    (∫ v : ℝ, ‖relativeVerticalExp d E t x y n v‖) ≤ verticalMassConstant η tmax := by
  have htm : 0 < tmax := lt_of_lt_of_le ht htmax
  have hn0 : 0 < n := lt_of_lt_of_le one_pos hn
  set T := verticalTailConstant η tmax with hT
  set R := Real.sqrt (8*tmax*|T|+tmax) with hR
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hRsq : R^2 = 8*tmax*|T|+tmax := Real.sq_sqrt (by positivity)
  have hy := levelHeight_eq_of_root hN d t x y ht hr
  have hyle : y ≤ Real.sqrt t := hy ▸ (levelHeight_bounds hN d t x ht).2
  have hy2 : y^2 ≤ R^2 := by
    have h1 : y^2 ≤ t := by
      have := pow_le_pow_left₀ hr.1.le hyle 2
      rwa [Real.sq_sqrt ht.le] at this
    rw [hRsq]; nlinarith [abs_nonneg T]
  have hint := (integrable_relativeVerticalExp hN d E t x y η tmax n ht hr hη hheight htmax
    hn0).norm
  set s : Set ℝ := {v : ℝ | R^2 ≤ v^2} with hs
  have hsm : MeasurableSet s := measurableSet_le measurable_const (by fun_prop)
  rw [← integral_add_compl hsm hint]
  -- tail
  have htail := integral_relativeVerticalExp_tail_le hN d E t x y η tmax n R ht hr hη hheight
    htmax hn0 hy2
  have hexp : Real.exp (n*T-n*R^2/(8*tmax)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    rw [hRsq]
    have h2 : n*(8*tmax*|T|+tmax)/(8*tmax) = n*|T| + n/8 := by field_simp
    rw [h2]
    nlinarith [le_abs_self T]
  have hsq : Real.sqrt (Real.pi/(n/(8*tmax))) ≤ Real.sqrt (8*Real.pi*tmax) := by
    apply Real.sqrt_le_sqrt
    rw [div_div_eq_mul_div]
    rw [div_le_iff₀ hn0]
    nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le htm.le) (sub_nonneg.mpr hn)]
  have ht1 : (∫ v in s, ‖relativeVerticalExp d E t x y n v‖) ≤ Real.sqrt (8*Real.pi*tmax) :=
    htail.trans ((mul_le_of_le_one_left (Real.sqrt_nonneg _) hexp).trans hsq)
  -- core
  have hcore : (∫ v in sᶜ, ‖relativeVerticalExp d E t x y n v‖) ≤ 2*R := by
    have hsub : sᶜ ⊆ Icc (-R) R := by
      intro v hv
      simp only [hs, mem_compl_iff, mem_ofPred_eq, not_le] at hv
      have := abs_lt_of_sq_lt_sq hv hR0
      exact ⟨by linarith [(abs_lt.mp this).1], by linarith [(abs_lt.mp this).2]⟩
    have hfin : volume sᶜ < ⊤ :=
      lt_of_le_of_lt (measure_mono hsub) (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
    have hb : ∀ᵐ v ∂(volume.restrict sᶜ), ‖‖relativeVerticalExp d E t x y n v‖‖ ≤ 1 := by
      have h0 : ({0} : Set ℝ)ᶜ ∈ ae volume := by
        rw [compl_mem_ae_iff]; exact measure_singleton _
      filter_upwards [ae_restrict_of_ae h0] with v hv
      have hv0 : v ≠ 0 := by simpa using hv
      rw [norm_norm, norm_relativeVerticalExp]
      apply Real.exp_le_one_iff.mpr
      have hdom : VerticalActionDomain d x v := fun j => by positivity
      have hmax := verticalRealAction_max hN d E t x v ht hdom
      rw [hy] at hmax
      nlinarith
    have h := norm_setIntegral_le_of_norm_le_const_ae hfin hb
    have hreal : volume.real sᶜ ≤ 2*R := by
      have h1 : volume.real sᶜ ≤ volume.real (Icc (-R) R) :=
        measureReal_mono hsub (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
      rw [Real.volume_real_Icc] at h1
      refine h1.trans (le_of_eq ?_)
      rw [max_eq_left (by linarith)]
      ring
    calc (∫ v in sᶜ, ‖relativeVerticalExp d E t x y n v‖)
        ≤ ‖∫ v in sᶜ, ‖relativeVerticalExp d E t x y n v‖‖ := le_abs_self _
      _ ≤ 1 * volume.real sᶜ := h
      _ ≤ 2*R := by rw [one_mul]; exact hreal
  unfold verticalMassConstant
  rw [← hT, ← hR]
  linarith

end BlockBand.GaussianBulk
