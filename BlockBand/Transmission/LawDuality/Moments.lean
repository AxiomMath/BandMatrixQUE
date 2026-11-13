module

public import BlockBand.Transmission.LawDuality.Ratio

/-!
# Determination: the moments of `ν` from the log-transforms `G_x(ν)`

The moments of a finite measure `ν` on `[0,1]` are limits of explicit combinations of the
log-transforms `G_{x_k}(ν)`, `x_k = 1/(k+2)`; hence they are measurable functions of them.

* `logKernel x t = log(1+xt)/t` (value `x` at `t = 0`), `logTransform x ν = ∫ logKernel x dν`,
  so `F_{x,0}(ν) = exp(-G_x(ν))` (`transmissionRatio_single_zero`).
* `abs_logKernel_sub_le`: `|logKernel x t - Σ_{i<J} (-1)^i x^{i+1}t^i/(i+1)| ≤ 2x^{J+1}t^J` for
  `0 ≤ x ≤ 1/2`, `t ∈ [0,1]` (alternating log series).
* **`measurable_moment_of`**: for any measurable space `α` and `ν : α → FiniteMeasure [0,1]`,
  if every `a ↦ G_{x_k}(ν a)` is measurable, then so is every moment `a ↦ ∫ t^J dν(a)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Transmission.DualBoundary
open scoped NNReal ENNReal BoundedContinuousFunction

/-- `φ_x(t) = log(1+xt)/t`, `φ_x(0) = x`. -/
def logKernel (x t : ℝ) : ℝ := -ratioIntegrand ![x] ![0] t

theorem logKernel_eq (x t : ℝ) :
    logKernel x t = if t = 0 then x else Real.log (1 + x * t) / t := by
  rw [logKernel, ratioIntegrand_one]
  split_ifs <;> simp [neg_div]

/-- `G_x(ν) = ∫ φ_x dν`. -/
def logTransform (x : ℝ) (ν : FiniteMeasure unitInterval) : ℝ :=
  ∫ t, logKernel x (t : ℝ) ∂(ν : Measure unitInterval)

/-- The moments `m_j(ν) = ∫ t^j dν(t)`. -/
def moment (j : ℕ) (ν : FiniteMeasure unitInterval) : ℝ :=
  ∫ t, (t : ℝ) ^ j ∂(ν : Measure unitInterval)

/-- The evaluation points `x_k = 1/(k+2) ∈ (0, 1/2]`. -/
def evalPoint (k : ℕ) : ℝ := 1 / ((k : ℝ) + 2)

theorem evalPoint_pos (k : ℕ) : 0 < evalPoint k := by unfold evalPoint; positivity

theorem evalPoint_le (k : ℕ) : evalPoint k ≤ 1 / 2 := by
  unfold evalPoint
  exact one_div_le_one_div_of_le (by norm_num) (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])

theorem tendsto_evalPoint : Tendsto evalPoint atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)

theorem transmissionRatio_single_zero (x : ℝ) (ν : FiniteMeasure unitInterval) :
    transmissionRatio ![x] ![0] ν = Real.exp (-logTransform x ν) := by
  unfold transmissionRatio logTransform logKernel
  rw [integral_neg, neg_neg]

theorem integrable_logKernel {x : ℝ} (hx : 0 ≤ x) (ν : FiniteMeasure unitInterval) :
    Integrable (fun t : unitInterval => logKernel x (t : ℝ)) (ν : Measure unitInterval) :=
  ((ratioBCF hx le_rfl zero_lt_one).integrable _).neg

theorem integrable_pow (j : ℕ) (ν : FiniteMeasure unitInterval) :
    Integrable (fun t : unitInterval => (t : ℝ) ^ j) (ν : Measure unitInterval) :=
  (BoundedContinuousFunction.mkOfCompact
    ⟨fun t : unitInterval => (t : ℝ) ^ j, continuous_subtype_val.pow j⟩).integrable _

/-- The Taylor polynomial `Σ_{i<J} (-1)^i x^{i+1}t^i/(i+1)` of `φ_x(t)` in `x`. -/
def kernelTaylor (J : ℕ) (x t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range J, (-1) ^ i * x ^ (i + 1) / ((i : ℝ) + 1) * t ^ i

/-- `S_J(x, ν) = Σ_{i<J} (-1)^i x^{i+1} m_i(ν)/(i+1)`. -/
def momentTaylor (J : ℕ) (x : ℝ) (ν : FiniteMeasure unitInterval) : ℝ :=
  ∑ i ∈ Finset.range J, (-1) ^ i * x ^ (i + 1) / ((i : ℝ) + 1) * moment i ν

theorem abs_logKernel_sub_le {x t : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (J : ℕ) :
    |logKernel x t - kernelTaylor J x t| ≤ 2 * x ^ (J + 1) * t ^ J := by
  rw [logKernel_eq]
  rcases eq_or_lt_of_le ht0 with h | h
  · subst h
    simp only [↓reduceIte]
    rcases J with _ | J
    · simp only [kernelTaylor, Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero,
        mul_one, zero_add, pow_one, abs_of_nonneg hx0]
      linarith
    · rw [kernelTaylor, Finset.sum_range_succ']
      simp
  · have ht : t ≠ 0 := h.ne'
    simp only [ht, ↓reduceIte]
    have hu0 : 0 ≤ x * t := mul_nonneg hx0 ht0
    have hu1 : x * t ≤ 1 / 2 := by
      have : x * t ≤ x * 1 := mul_le_mul_of_nonneg_left ht1 hx0
      linarith
    have hm := Real.abs_log_sub_add_sum_range_le (x := -(x * t))
      (by rw [abs_neg, abs_of_nonneg hu0]; linarith) J
    rw [abs_neg, abs_of_nonneg hu0, sub_neg_eq_add] at hm
    have hb : (x * t) ^ (J + 1) / (1 - x * t) ≤ 2 * (x * t) ^ (J + 1) := by
      rw [div_le_iff₀ (by linarith)]
      have : 0 ≤ (x * t) ^ (J + 1) := pow_nonneg hu0 _
      nlinarith
    have hT : kernelTaylor J x t =
        -(∑ i ∈ Finset.range J, (-(x * t)) ^ (i + 1) / ((i : ℝ) + 1)) / t := by
      rw [kernelTaylor, eq_div_iff ht, Finset.sum_mul, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [neg_pow (x * t) (i + 1), mul_pow, pow_succ (-1 : ℝ), pow_succ t]
      field_simp
    have key : Real.log (1 + x * t) / t - kernelTaylor J x t =
        (∑ i ∈ Finset.range J, (-(x * t)) ^ (i + 1) / ((i : ℝ) + 1) +
          Real.log (1 + x * t)) / t := by
      rw [hT]; ring
    rw [key, abs_div, abs_of_pos h, div_le_iff₀ h]
    calc _ ≤ 2 * (x * t) ^ (J + 1) := hm.trans hb
      _ = 2 * x ^ (J + 1) * t ^ J * t := by rw [mul_pow, pow_succ t]; ring

theorem integrable_kernelTaylor (J : ℕ) (x : ℝ) (ν : FiniteMeasure unitInterval) :
    Integrable (fun t : unitInterval => kernelTaylor J x (t : ℝ)) (ν : Measure unitInterval) :=
  integrable_finsetSum _ fun i _ => (integrable_pow i ν).const_mul _

theorem integral_kernelTaylor (J : ℕ) (x : ℝ) (ν : FiniteMeasure unitInterval) :
    ∫ t, kernelTaylor J x (t : ℝ) ∂(ν : Measure unitInterval) = momentTaylor J x ν := by
  unfold kernelTaylor momentTaylor
  rw [integral_finsetSum _ fun i _ => (integrable_pow i ν).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, moment]

theorem abs_logTransform_sub_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) (J : ℕ)
    (ν : FiniteMeasure unitInterval) :
    |logTransform x ν - momentTaylor J x ν| ≤
      2 * x ^ (J + 1) * (ν : Measure unitInterval).real univ := by
  rw [← integral_kernelTaylor, logTransform,
    ← integral_sub (integrable_logKernel hx0 ν) (integrable_kernelTaylor J x ν), ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le_const (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs]
  refine (abs_logKernel_sub_le hx0 hx1 t.2.1 t.2.2 J).trans ?_
  have : (t : ℝ) ^ J ≤ 1 := pow_le_one₀ t.2.1 t.2.2
  have : 0 ≤ 2 * x ^ (J + 1) := by positivity
  nlinarith

/-- The approximant `(-1)^J (J+1)(G_{x_k} - S_J(x_k))/x_k^{J+1}` of `m_J`. -/
def momentApprox (J k : ℕ) (ν : FiniteMeasure unitInterval) : ℝ :=
  (-1) ^ J * ((J : ℝ) + 1) * (logTransform (evalPoint k) ν - momentTaylor J (evalPoint k) ν) /
    evalPoint k ^ (J + 1)

theorem abs_momentApprox_sub_le (J k : ℕ) (ν : FiniteMeasure unitInterval) :
    |momentApprox J k ν - moment J ν| ≤
      2 * ((J : ℝ) + 1) * evalPoint k * (ν : Measure unitInterval).real univ := by
  unfold momentApprox
  have hx : 0 < evalPoint k := evalPoint_pos k
  set x := evalPoint k
  have hS : momentTaylor (J + 1) x ν =
      momentTaylor J x ν + (-1) ^ J * x ^ (J + 1) / ((J : ℝ) + 1) * moment J ν := by
    rw [momentTaylor, Finset.sum_range_succ]; rfl
  have hpow : (-1 : ℝ) ^ J * (-1) ^ J = 1 := by rw [← mul_pow]; norm_num
  have hJ : (0 : ℝ) < (J : ℝ) + 1 := by positivity
  have hm : (-1) ^ J * ((J : ℝ) + 1) * ((-1) ^ J * x ^ (J + 1) / ((J : ℝ) + 1) * moment J ν) /
      x ^ (J + 1) = moment J ν := by
    calc _ = ((-1) ^ J * (-1) ^ J) * moment J ν * (((J : ℝ) + 1) / ((J : ℝ) + 1)) *
          (x ^ (J + 1) / x ^ (J + 1)) := by ring
      _ = moment J ν := by
        rw [hpow, div_self hJ.ne', div_self (pow_pos hx _).ne']; ring
  have e : (-1) ^ J * ((J : ℝ) + 1) * (logTransform x ν - momentTaylor J x ν) / x ^ (J + 1) -
      moment J ν =
      (-1) ^ J * ((J : ℝ) + 1) * (logTransform x ν - momentTaylor (J + 1) x ν) / x ^ (J + 1) := by
    rw [hS]
    linear_combination hm
  rw [e, abs_div, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos hJ, abs_of_pos (pow_pos hx _), div_le_iff₀ (pow_pos hx _)]
  have hb := abs_logTransform_sub_le hx.le (evalPoint_le k) (J + 1) ν
  calc ((J : ℝ) + 1) * |logTransform x ν - momentTaylor (J + 1) x ν|
      ≤ ((J : ℝ) + 1) * (2 * x ^ (J + 1 + 1) * (ν : Measure unitInterval).real univ) :=
        mul_le_mul_of_nonneg_left hb hJ.le
    _ = _ := by ring

theorem tendsto_momentApprox (J : ℕ) (ν : FiniteMeasure unitInterval) :
    Tendsto (fun k => momentApprox J k ν) atTop (𝓝 (moment J ν)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h : Tendsto (fun k => 2 * ((J : ℝ) + 1) * evalPoint k * (ν : Measure unitInterval).real univ)
      atTop (𝓝 (2 * ((J : ℝ) + 1) * 0 * (ν : Measure unitInterval).real univ)) :=
    ((tendsto_evalPoint.const_mul _).mul_const _)
  rw [mul_zero, zero_mul] at h
  exact squeeze_zero (fun _ => norm_nonneg _) (fun k => abs_momentApprox_sub_le J k ν) h

/-- **The moments are measurable functions of the log-transforms at `x_k`.** -/
theorem measurable_moment_of {α : Type*} [MeasurableSpace α] {ν : α → FiniteMeasure unitInterval}
    (h : ∀ k, Measurable fun a => logTransform (evalPoint k) (ν a)) (J : ℕ) :
    Measurable fun a => moment J (ν a) := by
  induction J using Nat.strong_induction_on with
  | _ J ih =>
    have hT : ∀ k, Measurable fun a => momentTaylor J (evalPoint k) (ν a) := fun k =>
      Finset.measurable_sum _ fun i hi => (ih i (Finset.mem_range.1 hi)).const_mul _
    have hA : ∀ k, Measurable fun a => momentApprox J k (ν a) := fun k => by
      have h1 := h k
      have h2 := hT k
      unfold momentApprox
      fun_prop
    exact measurable_of_tendsto_metrizable hA (tendsto_pi_nhds.2 fun a => tendsto_momentApprox J _)

end BlockBand.Transmission.LawDuality
