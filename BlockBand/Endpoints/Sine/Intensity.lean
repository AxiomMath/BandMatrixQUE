module

public import BlockBand.Endpoints.Sine.FredholmSeries
public import BlockBand.Model.Construction.VagueTranslation

/-!
# First intensity from a Fredholm Laplace functional

If the Laplace functional of a point process on `ℝ` is the Fredholm series of a kernel `K` with
Gram determinants bounded by one and `K x x = 1` against a locally finite measure `ν`, then its
first intensity is `ν`: `E ξ(g) = ∫ g dν` for nonnegative `g ∈ C_c(ℝ)`
(`lintegral_coordinate_eq_of_fredholm`, `integral_coordinate_eq_of_fredholm`). The proof
differentiates `t ↦ E exp(-t ξ(g))` at `0⁺` along `t_n = 1/(n+1)`, using the first-order
Fredholm expansion.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Set
open scoped Topology ENNReal

/-- The sequence `t n = 1 / (n + 1)` used to differentiate at `0⁺`. -/
def intensityStep (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

/-- `0 < intensityStep n` for every `n : ℕ`. -/
theorem intensityStep_pos (n : ℕ) : 0 < intensityStep n := by
  unfold intensityStep; positivity

/-- `intensityStep n ≤ 1` for every `n : ℕ`. -/
theorem intensityStep_le_one (n : ℕ) : intensityStep n ≤ 1 := by
  unfold intensityStep
  rw [div_le_one (by positivity)]
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- `intensityStep n → 0` as `n → ∞`. -/
theorem tendsto_intensityStep : Tendsto intensityStep atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- For real `s ≥ 0`: `0 ≤ 1 - exp (-s) ≤ s`. -/
theorem one_sub_exp_neg_mem (s : ℝ) (hs : 0 ≤ s) :
    0 ≤ 1 - Real.exp (-s) ∧ 1 - Real.exp (-s) ≤ s := by
  constructor
  · have : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.2 (neg_nonpos.2 hs)
    linarith
  · have := Real.add_one_le_exp (-s)
    linarith

/-- For real `0 ≤ s ≤ 1`: `s - s ^ 2 ≤ 1 - exp (-s)`. -/
theorem sub_sq_le_one_sub_exp_neg (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    s - s ^ 2 ≤ 1 - Real.exp (-s) := by
  have h := Real.abs_exp_sub_one_sub_id_le (x := -s) (by rw [abs_neg, abs_of_nonneg hs]; exact hs1)
  have h2 := (abs_le.mp h).2
  rw [neg_sq] at h2
  linarith

/-- For `a ≥ 0` and `t > 0`: `0 ≤ (1 - exp (-(t * a))) / t ≤ a`. -/
theorem one_sub_exp_div_mem (a t : ℝ) (ha : 0 ≤ a) (ht : 0 < t) :
    0 ≤ (1 - Real.exp (-(t * a))) / t ∧ (1 - Real.exp (-(t * a))) / t ≤ a := by
  obtain ⟨h0, h1⟩ := one_sub_exp_neg_mem (t * a) (mul_nonneg ht.le ha)
  refine ⟨div_nonneg h0 ht.le, ?_⟩
  rw [div_le_iff₀ ht]
  linarith

/-- For `a ≥ 0`, `(1 - exp (-(t n * a))) / t n → a` along `t n = 1/(n+1)`. -/
theorem tendsto_one_sub_exp_div (a : ℝ) (ha : 0 ≤ a) :
    Tendsto (fun n => (1 - Real.exp (-(intensityStep n * a))) / intensityStep n) atTop
      (𝓝 a) := by
  have hlow : Tendsto (fun n => a - intensityStep n * a ^ 2) atTop (𝓝 a) := by
    simpa using tendsto_const_nhds.sub (tendsto_intensityStep.mul_const (a ^ 2))
  have hsmall : ∀ᶠ n in atTop, intensityStep n * a ≤ 1 := by
    have h := tendsto_intensityStep.mul_const a
    rw [zero_mul] at h
    exact h.eventually (ge_mem_nhds one_pos)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_
    (Eventually.of_forall fun n => (one_sub_exp_div_mem a _ ha (intensityStep_pos n)).2)
  filter_upwards [hsmall] with n hn
  have ht := intensityStep_pos n
  have h := sub_sq_le_one_sub_exp_neg (intensityStep n * a) (mul_nonneg ht.le ha) hn
  rw [le_div_iff₀ ht]
  nlinarith

/-- The first two Fredholm terms: `∑_{k < 2} fredholmTerm K ν φ k = 1 - ∫ K x x * φ x dν`
(any kernel, weight and measure). -/
theorem sum_range_two_fredholmTerm (K : ℝ → ℝ → ℝ) (ν : Measure ℝ) (φ : ℝ → ℝ) :
    ∑ k ∈ Finset.range 2, fredholmTerm K ν φ k = 1 - ∫ x, K x x * φ x ∂ν := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, fredholmTerm,
    fredholmIntegral_zero, fredholmIntegral_one]
  norm_num
  ring

/-- First-order Fredholm expansion. For σ-finite `ν`, `φ ∈ L¹(ν)` and a kernel with Gram
determinants bounded by one, with `A = ∫ |φ| dν`,
`|fredholmSeries K ν φ - (1 - ∫ K x x * φ x dν)| ≤ A ^ 2 / 2 * exp A`. -/
theorem abs_fredholmSeries_sub_first_le {K : ℝ → ℝ → ℝ}
    (hdet : ∀ (k : ℕ) (x : Fin k → ℝ), |Matrix.det (fun i j : Fin k => K (x i) (x j))| ≤ 1)
    {ν : Measure ℝ} [SigmaFinite ν] {φ : ℝ → ℝ} (hφ : Integrable φ ν) :
    |fredholmSeries K ν φ - (1 - ∫ x, K x x * φ x ∂ν)| ≤
      (∫ x, |φ x| ∂ν) ^ 2 / 2 * Real.exp (∫ x, |φ x| ∂ν) := by
  have h := abs_fredholmSeries_sub_sum_le hdet hφ 2
  rw [sum_range_two_fredholmTerm] at h
  simpa using h

/-- Intensity from a Fredholm Laplace functional (lower-integral form). Let `P` be a law on
locally finite point measures on `ℝ`, `K` a kernel with all Gram determinants bounded by one and
`K x x = 1`, and `ν` a locally finite measure on `ℝ`. If for every nonnegative `f ∈ C_c(ℝ)` the
Laplace functional `E_P exp (-ξ(f))` equals `fredholmSeries K ν (1 - exp (-f))`, then for every
nonnegative `g ∈ C_c(ℝ)`, `∫⁻ ofReal (ξ(g)) dP = ofReal (∫ g dν)`. -/
theorem lintegral_coordinate_eq_of_fredholm
    (P : ProbabilityMeasure (VaguePointMeasure ℝ)) {K : ℝ → ℝ → ℝ}
    (hdet : ∀ (k : ℕ) (x : Fin k → ℝ), |Matrix.det (fun i j : Fin k => K (x i) (x j))| ≤ 1)
    (hdiag : ∀ x, K x x = 1) (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (hLap : ∀ f : CompactlySupportedContinuousMap ℝ ℝ, (∀ x, 0 ≤ f x) →
      ∫ ξ, Real.exp (-∫ x, f x ∂ξ.measure) ∂(P : Measure (VaguePointMeasure ℝ)) =
        fredholmSeries K ν (fun x => 1 - Real.exp (-f x)))
    (g : CompactlySupportedContinuousMap ℝ ℝ) (hg : ∀ x, 0 ≤ g x) :
    ∫⁻ ξ, ENNReal.ofReal (∫ x, g x ∂ξ.measure) ∂(P : Measure (VaguePointMeasure ℝ)) =
      ENNReal.ofReal (∫ x, g x ∂ν) := by
  set μ : Measure (VaguePointMeasure ℝ) := (P : Measure (VaguePointMeasure ℝ)) with hμ
  set G : ℝ := ∫ x, g x ∂ν with hG
  have hgi : Integrable g ν := g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
  have hG0 : 0 ≤ G := integral_nonneg hg
  -- the random linear statistic
  set Λ : VaguePointMeasure ℝ → ℝ := fun ξ => ∫ x, g x ∂ξ.measure with hΛ
  have hΛm : Measurable Λ :=
    (BlockBand.Model.Construction.continuous_vaguePointMeasure_coordinate g).measurable
  have hΛ0 (ξ : VaguePointMeasure ℝ) : 0 ≤ Λ ξ := integral_nonneg hg
  set t := intensityStep with ht
  -- the difference quotients, pointwise in `ξ`
  set f : ℕ → VaguePointMeasure ℝ → ℝ :=
    fun n ξ => (1 - Real.exp (-(t n * Λ ξ))) / t n with hf
  have hfm (n : ℕ) : Measurable (f n) := by
    refine Measurable.div_const (measurable_const.sub ?_) _
    exact Real.measurable_exp.comp ((hΛm.const_mul _).neg)
  have hfmem (n : ℕ) (ξ : VaguePointMeasure ℝ) := one_sub_exp_div_mem (Λ ξ) (t n) (hΛ0 ξ)
    (intensityStep_pos n)
  have hfi (n : ℕ) : Integrable (f n) μ := by
    refine Integrable.of_bound (hfm n).aestronglyMeasurable (1 / t n)
      (Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hfmem n ξ).1]
    have hpos := intensityStep_pos n
    refine div_le_div_of_nonneg_right ?_ hpos.le
    have : 0 < Real.exp (-(t n * Λ ξ)) := Real.exp_pos _
    linarith
  -- the weights `φ_n = 1 - exp (-(t n * g))`
  set φ : ℕ → ℝ → ℝ := fun n x => 1 - Real.exp (-(t n * g x)) with hφ
  have hφmem (n : ℕ) (x : ℝ) := one_sub_exp_neg_mem (t n * g x)
    (mul_nonneg (intensityStep_pos n).le (hg x))
  have hφi (n : ℕ) : Integrable (φ n) ν := by
    refine (hgi.const_mul (t n)).mono' ?_ (Eventually.of_forall fun x => ?_)
    · exact (continuous_const.sub (Real.continuous_exp.comp
        ((continuous_const.mul g.continuous).neg))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (hφmem n x).1]
      exact (hφmem n x).2
  -- expectation of the difference quotient via the Laplace functional
  have hcn (n : ℕ) : ∫ ξ, f n ξ ∂μ = (1 - fredholmSeries K ν (φ n)) / t n := by
    have hL := hLap (t n • g) fun x => by
      rw [CompactlySupportedContinuousMap.smul_apply, smul_eq_mul]
      exact mul_nonneg (intensityStep_pos n).le (hg x)
    simp only [CompactlySupportedContinuousMap.smul_apply, smul_eq_mul, integral_const_mul]
      at hL
    have hei : Integrable (fun ξ : VaguePointMeasure ℝ => Real.exp (-(t n * Λ ξ))) μ := by
      refine Integrable.of_bound (Real.measurable_exp.comp
        ((hΛm.const_mul _).neg)).aestronglyMeasurable 1 (Eventually.of_forall fun ξ => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
      exact mul_nonneg (intensityStep_pos n).le (hΛ0 ξ)
    simp only [hf]
    rw [integral_div, integral_sub (integrable_const 1) hei, integral_const, hL]
    simp
    rfl
  -- the deterministic difference quotients converge to `G`
  set c : ℕ → ℝ := fun n => (1 - fredholmSeries K ν (φ n)) / t n with hc
  have hc_tendsto : Tendsto c atTop (𝓝 G) := by
    have hmain : Tendsto (fun n => ∫ x, φ n x / t n ∂ν) atTop (𝓝 G) := by
      refine tendsto_integral_of_dominated_convergence g (fun n => ?_) hgi
        (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
      · exact ((hφi n).div_const _).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_of_nonneg (one_sub_exp_div_mem (g x) (t n) (hg x) (intensityStep_pos n)).1]
        exact (one_sub_exp_div_mem (g x) (t n) (hg x) (intensityStep_pos n)).2
      · exact tendsto_one_sub_exp_div (g x) (hg x)
    have hdiagφ (n : ℕ) : ∫ x, K x x * φ n x ∂ν = ∫ x, φ n x ∂ν := by simp_rw [hdiag, one_mul]
    have hA (n : ℕ) : ∫ x, |φ n x| ∂ν ≤ t n * G := by
      rw [hG, ← integral_const_mul]
      exact integral_mono (hφi n).abs (hgi.const_mul _) fun x => by
        rw [abs_of_nonneg (hφmem n x).1]; exact (hφmem n x).2
    have hA0 (n : ℕ) : 0 ≤ ∫ x, |φ n x| ∂ν := integral_nonneg fun _ => abs_nonneg _
    have hR (n : ℕ) : |(fredholmSeries K ν (φ n) - (1 - ∫ x, φ n x ∂ν)) / t n| ≤
        t n * (G ^ 2 / 2 * Real.exp G) := by
      have h := abs_fredholmSeries_sub_first_le hdet (hφi n)
      rw [hdiagφ] at h
      have htn := intensityStep_pos n
      have htn1 := intensityStep_le_one n
      rw [abs_div, abs_of_pos htn, div_le_iff₀ htn]
      refine h.trans ?_
      have h1 : ∫ x, |φ n x| ∂ν ≤ G := (hA n).trans (by nlinarith)
      have h2 : (∫ x, |φ n x| ∂ν) ^ 2 ≤ (t n * G) ^ 2 := pow_le_pow_left₀ (hA0 n) (hA n) 2
      have h3 : Real.exp (∫ x, |φ n x| ∂ν) ≤ Real.exp G := Real.exp_le_exp.2 h1
      calc _ ≤ (t n * G) ^ 2 / 2 * Real.exp G :=
            mul_le_mul (div_le_div_of_nonneg_right h2 two_pos.le) h3 (Real.exp_pos _).le
              (by positivity)
        _ = _ := by ring
    have hRt : Tendsto (fun n => (fredholmSeries K ν (φ n) - (1 - ∫ x, φ n x ∂ν)) / t n)
        atTop (𝓝 0) := by
      refine squeeze_zero_norm (a := fun n => t n * (G ^ 2 / 2 * Real.exp G))
        (fun n => by rw [Real.norm_eq_abs]; exact hR n) ?_
      simpa using tendsto_intensityStep.mul_const (G ^ 2 / 2 * Real.exp G)
    have heq : c = fun n => ∫ x, φ n x / t n ∂ν -
        (fredholmSeries K ν (φ n) - (1 - ∫ x, φ n x ∂ν)) / t n := by
      funext n
      rw [integral_div]
      simp only [hc]
      ring
    rw [heq]
    simpa using hmain.sub hRt
  have hcn' (n : ℕ) : ∫⁻ ξ, ENNReal.ofReal (f n ξ) ∂μ = ENNReal.ofReal (c n) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hfi n)
      (Eventually.of_forall fun ξ => (hfmem n ξ).1), hcn]
  have hcE : Tendsto (fun n => ENNReal.ofReal (c n)) atTop (𝓝 (ENNReal.ofReal G)) :=
    (ENNReal.continuous_ofReal.tendsto _).comp hc_tendsto
  apply le_antisymm
  · calc ∫⁻ ξ, ENNReal.ofReal (Λ ξ) ∂μ
          = ∫⁻ ξ, liminf (fun n => ENNReal.ofReal (f n ξ)) atTop ∂μ := by
          refine lintegral_congr fun ξ => ?_
          exact ((ENNReal.continuous_ofReal.tendsto _).comp
            (tendsto_one_sub_exp_div (Λ ξ) (hΛ0 ξ))).liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ ξ, ENNReal.ofReal (f n ξ) ∂μ) atTop :=
          lintegral_liminf_le fun n => ENNReal.measurable_ofReal.comp (hfm n)
      _ = ENNReal.ofReal G := by
          simp_rw [hcn']
          exact hcE.liminf_eq
  · refine le_of_tendsto' hcE fun n => ?_
    rw [← hcn']
    exact lintegral_mono fun ξ => ENNReal.ofReal_le_ofReal (hfmem n ξ).2

/-- Intensity from a Fredholm Laplace functional (integrable form). Under the hypotheses of
`lintegral_coordinate_eq_of_fredholm`, for every nonnegative `g ∈ C_c(ℝ)` the linear statistic
`ξ ↦ ξ(g)` is `P`-integrable and `∫ ξ(g) dP = ∫ g dν`. -/
theorem integral_coordinate_eq_of_fredholm
    (P : ProbabilityMeasure (VaguePointMeasure ℝ)) {K : ℝ → ℝ → ℝ}
    (hdet : ∀ (k : ℕ) (x : Fin k → ℝ), |Matrix.det (fun i j : Fin k => K (x i) (x j))| ≤ 1)
    (hdiag : ∀ x, K x x = 1) (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (hLap : ∀ f : CompactlySupportedContinuousMap ℝ ℝ, (∀ x, 0 ≤ f x) →
      ∫ ξ, Real.exp (-∫ x, f x ∂ξ.measure) ∂(P : Measure (VaguePointMeasure ℝ)) =
        fredholmSeries K ν (fun x => 1 - Real.exp (-f x)))
    (g : CompactlySupportedContinuousMap ℝ ℝ) (hg : ∀ x, 0 ≤ g x) :
    Integrable (fun ξ : VaguePointMeasure ℝ => ∫ x, g x ∂ξ.measure)
        (P : Measure (VaguePointMeasure ℝ)) ∧
      ∫ ξ, (∫ x, g x ∂ξ.measure) ∂(P : Measure (VaguePointMeasure ℝ)) = ∫ x, g x ∂ν := by
  have hL := lintegral_coordinate_eq_of_fredholm P hdet hdiag ν hLap g hg
  have hm : Measurable (fun ξ : VaguePointMeasure ℝ => ∫ x, g x ∂ξ.measure) :=
    (BlockBand.Model.Construction.continuous_vaguePointMeasure_coordinate g).measurable
  have h0 : 0 ≤ᵐ[(P : Measure (VaguePointMeasure ℝ))]
      (fun ξ : VaguePointMeasure ℝ => ∫ x, g x ∂ξ.measure) :=
    Eventually.of_forall fun ξ => integral_nonneg hg
  refine ⟨⟨hm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal h0).2 ?_⟩, ?_⟩
  · rw [hL]; exact ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae h0 hm.aestronglyMeasurable, hL,
      ENNReal.toReal_ofReal (integral_nonneg hg)]

end BlockBand.Endpoints
