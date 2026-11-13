module

public import Mathlib
public import BlockBand.GaussianCalculus.ProductDensity

/-!
# Moments of complex linear forms of a Gaussian product vector

For `y ~ gaussianProduct v` on `ι → ℝ` (finite `ι`, every variance `v i ≥ 0`, zero allowed) and
complex coefficients `c`, every moment of order
`p > 0` satisfies `E‖∑ᵢ yᵢ cᵢ‖^p ≤ 4 (√p (∑ᵢ vᵢ‖cᵢ‖²)^{1/2})^p`, from the exact Gaussian
Laplace transform of linear forms and an elementary exponential bound.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.GaussianCalculus

open MeasureTheory ProbabilityTheory Set
open BlockBand.Internal.Contracts.Inputs (gaussianProduct)
open scoped NNReal ENNReal

variable {ι : Type} [Fintype ι]

/-- Elementary bound `u^p ≤ (A/e)^p exp((p/A) u)` for `u ≥ 0`, `p > 0`, `A > 0`. -/
theorem rpow_le_div_exp_rpow_mul_exp {p A u : ℝ} (hp : 0 < p) (hA : 0 < A) (hu : 0 ≤ u) :
    u ^ p ≤ (A / Real.exp 1) ^ p * Real.exp (p / A * u) := by
  set t := u / A with ht
  have ht0 : 0 ≤ t := div_nonneg hu hA.le
  have hu' : u = t * A := by rw [ht, div_mul_cancel₀ u hA.ne']
  have h1 : t ≤ Real.exp (t - 1) := by linarith [Real.add_one_le_exp (t - 1)]
  have h2 : t ^ p ≤ Real.exp (t - 1) ^ p := Real.rpow_le_rpow ht0 h1 hp.le
  rw [← Real.exp_mul] at h2
  have he : (A / Real.exp 1) ^ p = A ^ p / Real.exp p := by
    rw [Real.div_rpow hA.le (Real.exp_pos 1).le, Real.exp_one_rpow]
  have hexp : Real.exp ((t - 1) * p) = Real.exp (p / A * u) / Real.exp p := by
    rw [← Real.exp_sub]
    congr 1
    rw [hu']
    field_simp
  calc u ^ p = A ^ p * t ^ p := by rw [hu', Real.mul_rpow ht0 hA.le, mul_comm]
    _ ≤ A ^ p * Real.exp ((t - 1) * p) :=
      mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hA.le p)
    _ = (A / Real.exp 1) ^ p * Real.exp (p / A * u) := by
      rw [hexp, he]
      ring

/-- `exp(s|t|) ≤ exp(st) + exp(-st)` for `s ≥ 0`. -/
theorem exp_mul_abs_le (s t : ℝ) :
    Real.exp (s * |t|) ≤ Real.exp (s * t) + Real.exp (-(s * t)) := by
  rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]
    linarith [Real.exp_pos (-(s * t))]
  · rw [h, mul_neg]
    linarith [Real.exp_pos (s * t)]

/-- Exact Gaussian Laplace transform of a linear form under `gaussianProduct v`. -/
theorem lintegral_exp_linear (v : ι → ℝ≥0) (d : ι → ℝ) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (∑ i, d i * y i)) ∂gaussianProduct v =
      ENNReal.ofReal (Real.exp (∑ i, (v i : ℝ) * d i ^ 2 / 2)) := by
  have hγ : ∀ i, IsProbabilityMeasure (gaussianReal 0 (v i)) := fun i =>
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0 (v i)
  have hint : Integrable (fun y : ι → ℝ => ∏ i, Real.exp (d i * y i)) (gaussianProduct v) :=
    Integrable.fintype_prod (f := fun i (t : ℝ) => Real.exp (d i * t))
      fun i => integrable_exp_mul_gaussianReal (d i)
  simp_rw [Real.exp_sum]
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun y => (Finset.prod_pos fun i _ => Real.exp_pos _).le)]
  congr 1
  rw [gaussianProduct, integral_fintype_prod_eq_prod (f := fun i (t : ℝ) => Real.exp (d i * t))]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h := congrFun (mgf_id_gaussianReal (μ := 0) (v := v i)) (d i)
  simp only [mgf, id] at h
  rw [h]
  congr 1
  ring

/-- Sign-twisted Laplace transform bound used for the real and imaginary parts. -/
theorem lintegral_exp_sign_le (v : ι → ℝ≥0) (a b : ι → ℝ) (s ε δ : ℝ) (hε : ε ^ 2 = 1)
    (hδ : δ ^ 2 = 1) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (∑ i, s * (ε * a i + δ * b i) * y i)) ∂gaussianProduct v ≤
      ENNReal.ofReal (Real.exp (s ^ 2 * ∑ i, (v i : ℝ) * (a i ^ 2 + b i ^ 2))) := by
  rw [lintegral_exp_linear]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hv : (0 : ℝ) ≤ v i := (v i).2
  have hsq : (ε * a i + δ * b i) ^ 2 ≤ 2 * (a i ^ 2 + b i ^ 2) := by
    nlinarith [sq_nonneg (ε * a i - δ * b i)]
  have hs : 0 ≤ s ^ 2 := sq_nonneg s
  calc (v i : ℝ) * (s * (ε * a i + δ * b i)) ^ 2 / 2
      = (v i : ℝ) * s ^ 2 * (ε * a i + δ * b i) ^ 2 / 2 := by ring
    _ ≤ (v i : ℝ) * s ^ 2 * (2 * (a i ^ 2 + b i ^ 2)) / 2 := by gcongr
    _ = s ^ 2 * ((v i : ℝ) * (a i ^ 2 + b i ^ 2)) := by ring

/-- Law `gaussianProduct v` on `ι → ℝ` (finite `ι`, any variances, zero allowed). For complex
coefficients `c` and every real `p > 0`, `E‖∑ᵢ yᵢ cᵢ‖^p ≤ 4 (√p · (∑ᵢ vᵢ‖cᵢ‖²)^{1/2})^p`; the
constant `4` is absolute. -/
theorem lintegral_enorm_linear_rpow_le (v : ι → ℝ≥0) (c : ι → ℂ) {p : ℝ} (hp : 0 < p) :
    ∫⁻ y, ‖∑ i, y i • c i‖ₑ ^ p ∂gaussianProduct v ≤
      ENNReal.ofReal (4 * (Real.sqrt p * Real.sqrt (∑ i, (v i : ℝ) * ‖c i‖ ^ 2)) ^ p) := by
  set S := ∑ i, (v i : ℝ) * ‖c i‖ ^ 2 with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => mul_nonneg (v i).2 (sq_nonneg _)
  rcases hS0.eq_or_lt with hS | hS
  · -- degenerate case: the linear form vanishes almost surely
    have hterm : ∀ i, (v i : ℝ) * ‖c i‖ ^ 2 = 0 :=
      fun i => (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (v j).2 (sq_nonneg _))).mp
        hS.symm i (Finset.mem_univ i)
    have hae : ∀ᵐ y ∂gaussianProduct v, ∑ i, y i • c i = 0 := by
      have hall : ∀ᵐ y ∂gaussianProduct v, ∀ i, y i • c i = 0 := by
        rw [ae_all_iff]
        intro i
        rcases mul_eq_zero.mp (hterm i) with h | h
        · have hv : v i = 0 := by exact_mod_cast h
          filter_upwards [ae_gaussianProduct_coord_eq_zero v i hv] with y hy
          rw [hy, zero_smul]
        · have hc : c i = 0 := by
            have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
            exact norm_eq_zero.mp this
          exact Filter.Eventually.of_forall fun y => by rw [hc, smul_zero]
      filter_upwards [hall] with y hy
      exact Finset.sum_eq_zero fun i _ => hy i
    have h0 : ∫⁻ y, ‖∑ i, y i • c i‖ₑ ^ p ∂gaussianProduct v = 0 := by
      rw [lintegral_congr_ae (g := fun _ => 0)]
      · exact lintegral_zero
      · filter_upwards [hae] with y hy
        rw [hy, enorm_zero, ENNReal.zero_rpow_of_pos hp]
    rw [h0]
    exact bot_le
  · set A := Real.sqrt p * Real.sqrt S with hAdef
    have hA : 0 < A := mul_pos (Real.sqrt_pos.mpr hp) (Real.sqrt_pos.mpr hS)
    set s := p / A with hsdef
    have hs0 : 0 ≤ s := div_nonneg hp.le hA.le
    have hsS : s ^ 2 * S = p := by
      rw [hsdef, hAdef, div_pow, mul_pow, Real.sq_sqrt hp.le, Real.sq_sqrt hS.le]
      field_simp
    let a : ι → ℝ := fun i => (c i).re
    let b : ι → ℝ := fun i => (c i).im
    have hab : ∑ i, (v i : ℝ) * (a i ^ 2 + b i ^ 2) = S := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    let E : ℝ → ℝ → (ι → ℝ) → ℝ≥0∞ := fun ε δ y =>
      ENNReal.ofReal (Real.exp (∑ i, s * (ε * a i + δ * b i) * y i))
    have hEm (ε δ : ℝ) : Measurable (E ε δ) := by
      refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ?_)
      exact Finset.measurable_sum _ fun i _ => measurable_const.mul (measurable_pi_apply i)
    have hEle (ε δ : ℝ) (hε : ε ^ 2 = 1) (hδ : δ ^ 2 = 1) :
        ∫⁻ y, E ε δ y ∂gaussianProduct v ≤ ENNReal.ofReal (Real.exp p) := by
      have := lintegral_exp_sign_le v a b s ε δ hε hδ
      rwa [hab, hsS] at this
    have hpt : ∀ y : ι → ℝ, ‖∑ i, y i • c i‖ₑ ^ p ≤
        ENNReal.ofReal ((A / Real.exp 1) ^ p) *
          (E 1 1 y + E 1 (-1) y + E (-1) 1 y + E (-1) (-1) y) := by
      intro y
      set α := ∑ i, y i * a i
      set β := ∑ i, y i * b i
      have hre : (∑ i, y i • c i).re = α := by
        rw [Complex.re_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [Complex.real_smul, Complex.re_ofReal_mul]
      have him : (∑ i, y i • c i).im = β := by
        rw [Complex.im_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [Complex.real_smul, Complex.im_ofReal_mul]
      have hlin (ε δ : ℝ) : ∑ i, s * (ε * a i + δ * b i) * y i = s * ε * α + s * δ * β := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      have hnorm : ‖∑ i, y i • c i‖ ≤ |α| + |β| := by
        rw [← hre, ← him]
        exact Complex.norm_le_abs_re_add_abs_im _
      have hexp : Real.exp (p / A * ‖∑ i, y i • c i‖) ≤
          Real.exp (∑ i, s * (1 * a i + 1 * b i) * y i) +
            Real.exp (∑ i, s * (1 * a i + -1 * b i) * y i) +
            Real.exp (∑ i, s * (-1 * a i + 1 * b i) * y i) +
            Real.exp (∑ i, s * (-1 * a i + -1 * b i) * y i) := by
        rw [hlin, hlin, hlin, hlin]
        calc Real.exp (p / A * ‖∑ i, y i • c i‖) ≤ Real.exp (s * |α| + s * |β|) := by
              rw [Real.exp_le_exp, ← mul_add]
              exact mul_le_mul_of_nonneg_left hnorm hs0
          _ = Real.exp (s * |α|) * Real.exp (s * |β|) := Real.exp_add _ _
          _ ≤ (Real.exp (s * α) + Real.exp (-(s * α))) *
                (Real.exp (s * β) + Real.exp (-(s * β))) :=
              mul_le_mul (exp_mul_abs_le s α) (exp_mul_abs_le s β) (Real.exp_pos _).le
                (by positivity)
          _ = _ := by
              simp only [add_mul, mul_add, ← Real.exp_add]
              ring_nf
      have hbound := rpow_le_div_exp_rpow_mul_exp hp hA (norm_nonneg (∑ i, y i • c i))
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le]
      calc ENNReal.ofReal (‖∑ i, y i • c i‖ ^ p)
          ≤ ENNReal.ofReal ((A / Real.exp 1) ^ p * Real.exp (p / A * ‖∑ i, y i • c i‖)) :=
            ENNReal.ofReal_le_ofReal hbound
        _ ≤ ENNReal.ofReal ((A / Real.exp 1) ^ p *
              (Real.exp (∑ i, s * (1 * a i + 1 * b i) * y i) +
                Real.exp (∑ i, s * (1 * a i + -1 * b i) * y i) +
                Real.exp (∑ i, s * (-1 * a i + 1 * b i) * y i) +
                Real.exp (∑ i, s * (-1 * a i + -1 * b i) * y i))) :=
            ENNReal.ofReal_le_ofReal
              (mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg (by positivity) p))
        _ = ENNReal.ofReal ((A / Real.exp 1) ^ p) *
              (E 1 1 y + E 1 (-1) y + E (-1) 1 y + E (-1) (-1) y) := by
            rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) p)]
            simp only [E]
            rw [ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_add (by positivity) (by positivity)]
    calc ∫⁻ y, ‖∑ i, y i • c i‖ₑ ^ p ∂gaussianProduct v
        ≤ ∫⁻ y, ENNReal.ofReal ((A / Real.exp 1) ^ p) *
            (E 1 1 y + E 1 (-1) y + E (-1) 1 y + E (-1) (-1) y) ∂gaussianProduct v :=
          lintegral_mono hpt
      _ = ENNReal.ofReal ((A / Real.exp 1) ^ p) *
            (∫⁻ y, E 1 1 y ∂gaussianProduct v + ∫⁻ y, E 1 (-1) y ∂gaussianProduct v +
              ∫⁻ y, E (-1) 1 y ∂gaussianProduct v + ∫⁻ y, E (-1) (-1) y ∂gaussianProduct v) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_add_right _ (hEm (-1) (-1)), lintegral_add_right _ (hEm (-1) 1),
            lintegral_add_right _ (hEm 1 (-1))]
      _ ≤ ENNReal.ofReal ((A / Real.exp 1) ^ p) *
            (ENNReal.ofReal (Real.exp p) + ENNReal.ofReal (Real.exp p) +
              ENNReal.ofReal (Real.exp p) + ENNReal.ofReal (Real.exp p)) := by
          gcongr
          · exact hEle 1 1 (by norm_num) (by norm_num)
          · exact hEle 1 (-1) (by norm_num) (by norm_num)
          · exact hEle (-1) 1 (by norm_num) (by norm_num)
          · exact hEle (-1) (-1) (by norm_num) (by norm_num)
      _ = ENNReal.ofReal (4 * A ^ p) := by
          have he : (A / Real.exp 1) ^ p * Real.exp p = A ^ p := by
            rw [Real.div_rpow hA.le (Real.exp_pos 1).le, Real.exp_one_rpow]
            field_simp
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) p)]
          congr 1
          linear_combination 4 * he

end BlockBand.GaussianCalculus
