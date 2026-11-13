module

public import BlockBand.Endpoints.Sine.Intensity
public import BlockBand.Counting.OpenIntervalEvaluation

/-!
# Simplicity of any law with the sine Laplace functional

If a law on locally finite point measures on `ℝ` has the sine Laplace functional and the sine Gram
determinants are bounded by one, then almost every configuration is simple
(`ae_isSimple_of_sineLaplace`). The proof bounds the Fredholm series on short intervals, which
gives an `O((b - a)³)` bound on the probability of two points in an interval of length `b - a`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Set
open scoped Topology ENNReal

/-- The sine kernel is jointly continuous, hence jointly Borel. -/
theorem measurable_sineKernel : Measurable (Function.uncurry sineKernel) :=
  (Real.continuous_sinc.comp (continuous_const.mul (continuous_fst.sub continuous_snd))).measurable

/-- The sine kernel has unit diagonal: `sineKernel x x = 1`. -/
theorem sineKernel_self (x : ℝ) : sineKernel x x = 1 := by
  simp [sineKernel, Real.sinc_zero]

/-- For every real `u`: `1 - u ^ 2 / 6 ≤ sinc u`. -/
theorem one_sub_sq_div_six_le_sinc (u : ℝ) : 1 - u ^ 2 / 6 ≤ Real.sinc u := by
  have key (v : ℝ) (hv : 0 ≤ v) : 1 - v ^ 2 / 6 ≤ Real.sinc v := by
    rcases hv.eq_or_lt with rfl | hv
    · simp [Real.sinc_zero]
    rw [Real.sinc_of_ne_zero hv.ne', le_div_iff₀ hv]
    have := Real.sin_ge_sub_cube hv.le
    nlinarith
  rcases le_total 0 u with hu | hu
  · exact key u hu
  · have := key (-u) (neg_nonneg.2 hu)
    rwa [Real.sinc_neg, neg_sq] at this

/-- For every real `u`: `1 - sinc u ^ 2 ≤ u ^ 2 / 3`. -/
theorem one_sub_sinc_sq_le (u : ℝ) : 1 - Real.sinc u ^ 2 ≤ u ^ 2 / 3 := by
  have h1 := one_sub_sq_div_six_le_sinc u
  have h2 := Real.sinc_le_one u
  have h3 := Real.neg_one_le_sinc u
  nlinarith

/-- The first three Fredholm terms:
`∑_{k < 3} fredholmTerm K ν φ k = 1 - ∫ K x x * φ x dν + fredholmIntegral K ν φ 2 / 2`. -/
theorem sum_range_three_fredholmTerm (K : ℝ → ℝ → ℝ) (ν : Measure ℝ) (φ : ℝ → ℝ) :
    ∑ k ∈ Finset.range 3, fredholmTerm K ν φ k =
      1 - (∫ x, K x x * φ x ∂ν) + fredholmIntegral K ν φ 2 / 2 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, fredholmTerm,
    fredholmIntegral_zero, fredholmIntegral_one, Nat.factorial_two]
  norm_num
  ring

/-- Lebesgue integral of a weight `0 ≤ φ ≤ 1` vanishing off `Ioo a b`, `a ≤ b`:
`∫ φ ≤ b - a`. -/
theorem integral_le_of_Ioo {φ : ℝ → ℝ} (hφ : Integrable φ volume) (hφ1 : ∀ x, φ x ≤ 1)
    {a b : ℝ} (hab : a ≤ b) (hzero : ∀ x, x ∉ Ioo a b → φ x = 0) :
    ∫ x, φ x ≤ b - a := by
  have hi : Integrable ((Ioo a b).indicator (1 : ℝ → ℝ)) volume :=
    (integrable_indicator_iff measurableSet_Ioo).2 (integrableOn_const (by simp))
  calc ∫ x, φ x ≤ ∫ x, (Ioo a b).indicator (1 : ℝ → ℝ) x :=
        integral_mono hφ hi fun x => by
          by_cases hx : x ∈ Ioo a b
          · rw [indicator_of_mem hx]; exact hφ1 x
          · rw [indicator_of_notMem hx, hzero x hx]
    _ = b - a := by rw [integral_indicator_one measurableSet_Ioo, Real.volume_real_Ioo_of_le hab]

/-- Second sine Fredholm integral of a nonnegative Lebesgue-integrable weight
`φ` vanishing off `Ioo a b` (`a ≤ b`), assuming the sine Gram determinants are
bounded by one: `fredholmIntegral sineKernel volume φ 2 ≤ π² (b-a)² / 3 * (∫ φ)²`. -/
theorem fredholmIntegral_two_sine_le
    (hdetS : ∀ (k : ℕ) (x : Fin k → ℝ),
      |Matrix.det (fun i j : Fin k => sineKernel (x i) (x j))| ≤ 1)
    {φ : ℝ → ℝ} (hφ : Integrable φ volume) (hφ0 : ∀ x, 0 ≤ φ x)
    {a b : ℝ} (hzero : ∀ x, x ∉ Ioo a b → φ x = 0) :
    fredholmIntegral sineKernel volume φ 2 ≤
      Real.pi ^ 2 * (b - a) ^ 2 / 3 * (∫ x, φ x) ^ 2 := by
  have hpow : (∫ x, φ x) ^ 2 =
      ∫ x : Fin 2 → ℝ, ∏ i : Fin 2, φ (x i) ∂Measure.pi (fun _ : Fin 2 => volume) := by
    rw [integral_fintype_prod_eq_pow, Fintype.card_fin]
  unfold fredholmIntegral
  rw [hpow, ← integral_const_mul]
  refine integral_mono (integrable_fredholmIntegrand measurable_sineKernel hdetS hφ 2)
    ((Integrable.fintype_prod (f := fun _ : Fin 2 => φ) fun _ => hφ).const_mul _)
    fun x => ?_
  have hd : Matrix.det (fun i j : Fin 2 => sineKernel (x i) (x j)) =
      sineKernel (x 0) (x 0) * sineKernel (x 1) (x 1) -
        sineKernel (x 0) (x 1) * sineKernel (x 1) (x 0) := Matrix.det_fin_two _
  simp only
  rw [hd, sineKernel_self, sineKernel_self, Fin.prod_univ_two]
  have hp : 0 ≤ φ (x 0) * φ (x 1) := mul_nonneg (hφ0 _) (hφ0 _)
  by_cases h0 : x 0 ∈ Ioo a b
  · by_cases h1 : x 1 ∈ Ioo a b
    · refine mul_le_mul_of_nonneg_right ?_ hp
      have hs : sineKernel (x 1) (x 0) = sineKernel (x 0) (x 1) := by
        unfold sineKernel
        rw [← Real.sinc_neg]
        ring_nf
      rw [hs, one_mul, ← sq]
      have hsq : (x 0 - x 1) ^ 2 ≤ (b - a) ^ 2 := by
        exact sq_le_sq' (by linarith [h0.1, h0.2, h1.1, h1.2])
          (by linarith [h0.1, h0.2, h1.1, h1.2])
      calc 1 - sineKernel (x 0) (x 1) ^ 2 ≤ (Real.pi * (x 0 - x 1)) ^ 2 / 3 :=
            one_sub_sinc_sq_le _
        _ = Real.pi ^ 2 * (x 0 - x 1) ^ 2 / 3 := by ring
        _ ≤ Real.pi ^ 2 * (b - a) ^ 2 / 3 := by gcongr
    · rw [hzero _ h1, mul_zero, mul_zero, mul_zero]
  · rw [hzero _ h0, zero_mul, mul_zero, mul_zero]

/-- **Sine Fredholm bound on a short interval.** Assume the sine Gram
determinants are bounded by one. For a Lebesgue-integrable weight `0 ≤ φ ≤ 1`
vanishing off `Ioo a b` with `a ≤ b ≤ a + 1`:
`fredholmSeries sineKernel volume φ ≤ 1 - ∫ φ + 3 (b - a) ^ 3`. -/
theorem fredholmSeries_sine_le_of_Ioo
    (hdetS : ∀ (k : ℕ) (x : Fin k → ℝ),
      |Matrix.det (fun i j : Fin k => sineKernel (x i) (x j))| ≤ 1)
    {φ : ℝ → ℝ} (hφ : Integrable φ volume) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1)
    {a b : ℝ} (hab : a ≤ b) (hb1 : b - a ≤ 1) (hzero : ∀ x, x ∉ Ioo a b → φ x = 0) :
    fredholmSeries sineKernel volume φ ≤ 1 - (∫ x, φ x) + 3 * (b - a) ^ 3 := by
  have hF2 := fredholmIntegral_two_sine_le hdetS hφ hφ0 hzero
  have hAδ : ∫ x, φ x ≤ b - a := integral_le_of_Ioo hφ hφ1 hab hzero
  set δ := b - a with hδ
  set A := ∫ x, φ x with hA
  have hA0 : 0 ≤ A := integral_nonneg hφ0
  have hδ0 : 0 ≤ δ := sub_nonneg.2 hab
  have habs : ∫ x, |φ x| = A := by
    rw [hA]
    congr 1
    funext x
    exact abs_of_nonneg (hφ0 x)
  have htail := abs_fredholmSeries_sub_sum_le hdetS hφ 3
  rw [habs, sum_range_three_fredholmTerm] at htail
  simp_rw [sineKernel_self, one_mul] at htail
  have h6 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [h6] at htail
  have hπ : Real.pi ^ 2 ≤ 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have he : Real.exp A ≤ 3 :=
    (Real.exp_le_exp.2 (hAδ.trans hb1)).trans (by linarith [Real.exp_one_lt_d9])
  have hA2 : A ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ hA0 hAδ 2
  have hA3 : A ^ 3 ≤ δ ^ 3 := pow_le_pow_left₀ hA0 hAδ 3
  have hδ4 : δ ^ 2 * δ ^ 2 ≤ δ ^ 3 := by
    have : δ ^ 2 * δ ^ 2 = δ ^ 3 * δ := by ring
    rw [this]
    exact mul_le_of_le_one_right (pow_nonneg hδ0 3) hb1
  have hπA : Real.pi ^ 2 * A ^ 2 ≤ 10 * δ ^ 2 := mul_le_mul hπ hA2 (sq_nonneg _) (by norm_num)
  have h1 : Real.pi ^ 2 * δ ^ 2 / 3 * A ^ 2 ≤ 10 * δ ^ 3 / 3 := by
    have : Real.pi ^ 2 * δ ^ 2 / 3 * A ^ 2 = δ ^ 2 * (Real.pi ^ 2 * A ^ 2) / 3 := by ring
    rw [this]
    have := mul_le_mul_of_nonneg_left hπA (sq_nonneg δ)
    linarith
  have h2 : A ^ 3 / 6 * Real.exp A ≤ δ ^ 3 / 6 * 3 :=
    mul_le_mul (div_le_div_of_nonneg_right hA3 (by norm_num)) he (Real.exp_pos _).le
      (by positivity)
  have hle := (abs_le.mp htail).2
  have hδ3 : 0 ≤ δ ^ 3 := pow_nonneg hδ0 3
  have hAv : (∫ x, φ x ∂volume) = A := rfl
  rw [hAv] at hle
  change _ ≤ 1 - A + 3 * δ ^ 3
  linarith

/-- **Expected interval mass.** For a law `P` whose Laplace functional is the
sine Laplace functional on nonnegative `C_c` tests, with sine Gram
determinants bounded by one, and `a ≤ b`:
`∫⁻ ξ(Ioo a b) dP ≤ ofReal (b - a)`. -/
theorem lintegral_mass_Ioo_le_of_sineLaplace (P : ProbabilityMeasure (VaguePointMeasure ℝ))
    (hdetS : ∀ (k : ℕ) (x : Fin k → ℝ),
      |Matrix.det (fun i j : Fin k => sineKernel (x i) (x j))| ≤ 1)
    (hLap : ∀ f : CompactlySupportedContinuousMap ℝ ℝ, (∀ x, 0 ≤ f x) →
      ∫ ξ, Real.exp (-∫ x, f x ∂ξ.measure) ∂(P : Measure (VaguePointMeasure ℝ)) =
        sineLaplaceFunctional f)
    (a b : ℝ) (hab : a ≤ b) :
    ∫⁻ ξ, ξ.measure (Ioo a b) ∂(P : Measure (VaguePointMeasure ℝ)) ≤ ENNReal.ofReal (b - a) := by
  have hLapF : ∀ f : CompactlySupportedContinuousMap ℝ ℝ, (∀ x, 0 ≤ f x) →
      ∫ ξ, Real.exp (-∫ x, f x ∂ξ.measure) ∂(P : Measure (VaguePointMeasure ℝ)) =
        fredholmSeries sineKernel volume (fun x => 1 - Real.exp (-f x)) :=
    fun f hf => (hLap f hf).trans (sineLaplaceFunctional_eq_fredholmSeries f)
  set h := BlockBand.Counting.openIntervalApprox a b with hh
  have hI (n : ℕ) := lintegral_coordinate_eq_of_fredholm P hdetS sineKernel_self volume hLapF
    (h n) fun x => (BlockBand.Counting.openIntervalApprox_range a b n x).1
  have hpt (ξ : VaguePointMeasure ℝ) : Tendsto (fun n => ENNReal.ofReal (∫ x, h n x ∂ξ.measure))
      atTop (𝓝 (ξ.measure (Ioo a b))) := by
    have hfin : ξ.measure (Ioo a b) ≠ ∞ :=
      (lt_of_le_of_lt (measure_mono Ioo_subset_Icc_self) (ξ.finite_on_compact _ isCompact_Icc)).ne
    have := (ENNReal.continuous_ofReal.tendsto _).comp
      (BlockBand.Counting.tendsto_integral_openIntervalApprox ξ a b)
    rw [Measure.real, ENNReal.ofReal_toReal hfin] at this
    exact this
  have hle (n : ℕ) : ENNReal.ofReal (∫ x, h n x) ≤ ENNReal.ofReal (b - a) :=
    ENNReal.ofReal_le_ofReal (integral_le_of_Ioo
      ((h n).continuous.integrable_of_hasCompactSupport (h n).hasCompactSupport)
      (fun x => (BlockBand.Counting.openIntervalApprox_range a b n x).2) hab
      fun x hx => BlockBand.Counting.openIntervalApprox_zero a b n hx)
  calc ∫⁻ ξ, ξ.measure (Ioo a b) ∂(P : Measure (VaguePointMeasure ℝ))
        = ∫⁻ ξ, liminf (fun n => ENNReal.ofReal (∫ x, h n x ∂ξ.measure)) atTop
            ∂(P : Measure (VaguePointMeasure ℝ)) :=
        lintegral_congr fun ξ => (hpt ξ).liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ ξ, ENNReal.ofReal (∫ x, h n x ∂ξ.measure)
          ∂(P : Measure (VaguePointMeasure ℝ))) atTop :=
        lintegral_liminf_le fun n => ENNReal.measurable_ofReal.comp
          (BlockBand.Model.Construction.continuous_vaguePointMeasure_coordinate (h n)).measurable
    _ ≤ ENNReal.ofReal (b - a) :=
        liminf_le_of_frequently_le' (Frequently.of_forall fun n => by rw [hI n]; exact hle n)

/-- **Short-interval gap probability.** Under the hypotheses of
`lintegral_mass_Ioo_le_of_sineLaplace`, for `a ≤ b ≤ a + 1`:
`P {ξ | ξ(Ioo a b) = 0} ≤ ofReal (1 - (b - a) + 3 (b - a) ^ 3)`. -/
theorem measure_mass_Ioo_eq_zero_le_of_sineLaplace
    (P : ProbabilityMeasure (VaguePointMeasure ℝ))
    (hdetS : ∀ (k : ℕ) (x : Fin k → ℝ),
      |Matrix.det (fun i j : Fin k => sineKernel (x i) (x j))| ≤ 1)
    (hLap : ∀ f : CompactlySupportedContinuousMap ℝ ℝ, (∀ x, 0 ≤ f x) →
      ∫ ξ, Real.exp (-∫ x, f x ∂ξ.measure) ∂(P : Measure (VaguePointMeasure ℝ)) =
        sineLaplaceFunctional f)
    (a b : ℝ) (hab : a ≤ b) (hb1 : b - a ≤ 1) :
    (P : Measure (VaguePointMeasure ℝ)) {ξ | ξ.measure (Ioo a b) = 0} ≤
      ENNReal.ofReal (1 - (b - a) + 3 * (b - a) ^ 3) := by
  set μ : Measure (VaguePointMeasure ℝ) := (P : Measure (VaguePointMeasure ℝ)) with hμ
  set Z := {ξ : VaguePointMeasure ℝ | ξ.measure (Ioo a b) = 0} with hZ
  have hZm : MeasurableSet Z :=
    BlockBand.Counting.measurable_vague_Ioo_mass a b (measurableSet_singleton 0)
  set h := BlockBand.Counting.openIntervalApprox a b with hh
  have hr := BlockBand.Counting.openIntervalApprox_range a b
  set ψ : ℕ → CompactlySupportedContinuousMap ℝ ℝ := fun n => (n : ℝ) • h n with hψdef
  have hψ (n : ℕ) (x : ℝ) : ψ n x = n * h n x := by
    simp only [hψdef, CompactlySupportedContinuousMap.smul_apply, smul_eq_mul]
  have hψ0 (n : ℕ) (x : ℝ) : 0 ≤ ψ n x := by
    rw [hψ]; exact mul_nonneg (Nat.cast_nonneg n) (hr n x).1
  have hψz (n : ℕ) (x : ℝ) (hx : x ∉ Ioo a b) : ψ n x = 0 := by
    rw [hψ, BlockBand.Counting.openIntervalApprox_zero a b n hx, Pi.zero_apply, mul_zero]
  set φ : ℕ → ℝ → ℝ := fun n x => 1 - Real.exp (-ψ n x) with hφ
  have hφmem (n : ℕ) (x : ℝ) := one_sub_exp_neg_mem (ψ n x) (hψ0 n x)
  have hφ1 (n : ℕ) (x : ℝ) : φ n x ≤ 1 := by
    have := Real.exp_pos (-ψ n x)
    simp only [hφ]; linarith
  have hφz (n : ℕ) (x : ℝ) (hx : x ∉ Ioo a b) : φ n x = 0 := by
    simp only [hφ]; rw [hψz n x hx, neg_zero, Real.exp_zero, sub_self]
  have hφi (n : ℕ) : Integrable (φ n) volume := by
    refine ((ψ n).continuous.integrable_of_hasCompactSupport (ψ n).hasCompactSupport).mono'
      ?_ (Eventually.of_forall fun x => ?_)
    · exact (continuous_const.sub (Real.continuous_exp.comp
        (ψ n).continuous.neg)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (hφmem n x).1]
      exact (hφmem n x).2
  have hstep (n : ℕ) : μ.real Z ≤ 1 - (∫ x, φ n x) + 3 * (b - a) ^ 3 := by
    have hL := hLap (ψ n) (hψ0 n)
    rw [sineLaplaceFunctional_eq_fredholmSeries] at hL
    have hFred := fredholmSeries_sine_le_of_Ioo hdetS (hφi n) (fun x => (hφmem n x).1)
      (hφ1 n) hab hb1 (hφz n)
    have hei : Integrable (fun ξ : VaguePointMeasure ℝ =>
        Real.exp (-∫ x, ψ n x ∂ξ.measure)) μ := by
      refine Integrable.of_bound (Real.measurable_exp.comp
        (BlockBand.Model.Construction.continuous_vaguePointMeasure_coordinate
          (ψ n)).measurable.neg).aestronglyMeasurable 1 (Eventually.of_forall fun ξ => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
      exact integral_nonneg (hψ0 n)
    have hcmp : μ.real Z ≤ ∫ ξ, Real.exp (-∫ x, ψ n x ∂ξ.measure) ∂μ := by
      rw [← integral_indicator_one hZm]
      refine integral_mono ((integrable_indicator_iff hZm).2 (integrable_const _).integrableOn)
        hei fun ξ => ?_
      by_cases hξ : ξ ∈ Z
      · rw [indicator_of_mem hξ, Pi.one_apply]
        have h0 : ∫ x, ψ n x ∂ξ.measure = 0 := by
          rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioo a b)
            (fun x hx => hψz n x hx), Measure.restrict_eq_zero.2 hξ, integral_zero_measure]
        rw [h0, neg_zero, Real.exp_zero]
      · rw [indicator_of_notMem hξ]; exact (Real.exp_pos _).le
    rw [hL] at hcmp
    exact hcmp.trans hFred
  have hlim : Tendsto (fun n => ∫ x, φ n x) atTop (𝓝 (b - a)) := by
    have hi : Integrable ((Ioo a b).indicator (1 : ℝ → ℝ)) volume :=
      (integrable_indicator_iff measurableSet_Ioo).2 (integrableOn_const (by simp))
    have := tendsto_integral_of_dominated_convergence (f := (Ioo a b).indicator (1 : ℝ → ℝ))
      ((Ioo a b).indicator (1 : ℝ → ℝ)) (fun n => (hφi n).aestronglyMeasurable) hi
      (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · rwa [integral_indicator_one measurableSet_Ioo, Real.volume_real_Ioo_of_le hab] at this
    · rw [Real.norm_eq_abs, abs_of_nonneg (hφmem n x).1]
      by_cases hx : x ∈ Ioo a b
      · rw [indicator_of_mem hx, Pi.one_apply]; exact hφ1 n x
      · rw [indicator_of_notMem hx]; exact le_of_eq (hφz n x hx)
    · by_cases hx : x ∈ Ioo a b
      · rw [indicator_of_mem hx, Pi.one_apply]
        have h1 : Tendsto (fun n => h n x) atTop (𝓝 1) := by
          have := BlockBand.Counting.tendsto_openIntervalApprox a b x
          rwa [indicator_of_mem hx] at this
        have h2 : Tendsto (fun n : ℕ => ψ n x) atTop atTop := by
          simp_rw [hψ]
          exact tendsto_natCast_atTop_atTop.atTop_mul_pos one_pos h1
        have h3 := Real.tendsto_exp_neg_atTop_nhds_zero.comp h2
        simpa [hφ, Function.comp_def] using (tendsto_const_nhds (x := (1 : ℝ))).sub h3
      · rw [indicator_of_notMem hx]
        simp_rw [hφz _ x hx]
        exact tendsto_const_nhds
  have hreal : μ.real Z ≤ 1 - (b - a) + 3 * (b - a) ^ 3 :=
    ge_of_tendsto' ((tendsto_const_nhds.sub hlim).add_const _) hstep
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ Z)]
  exact ENNReal.ofReal_le_ofReal hreal

/-- **Short-interval double-point probability.** Under the hypotheses of
`lintegral_mass_Ioo_le_of_sineLaplace`, for `a ≤ b ≤ a + 1`:
`P {ξ | 2 ≤ ξ(Ioo a b)} ≤ ofReal (3 (b - a) ^ 3)`. -/
theorem measure_two_le_mass_Ioo_le_of_sineLaplace
    (P : ProbabilityMeasure (VaguePointMeasure ℝ))
    (hdetS : ∀ (k : ℕ) (x : Fin k → ℝ),
      |Matrix.det (fun i j : Fin k => sineKernel (x i) (x j))| ≤ 1)
    (hLap : ∀ f : CompactlySupportedContinuousMap ℝ ℝ, (∀ x, 0 ≤ f x) →
      ∫ ξ, Real.exp (-∫ x, f x ∂ξ.measure) ∂(P : Measure (VaguePointMeasure ℝ)) =
        sineLaplaceFunctional f)
    (a b : ℝ) (hab : a ≤ b) (hb1 : b - a ≤ 1) :
    (P : Measure (VaguePointMeasure ℝ)) {ξ | 2 ≤ ξ.measure (Ioo a b)} ≤
      ENNReal.ofReal (3 * (b - a) ^ 3) := by
  set μ : Measure (VaguePointMeasure ℝ) := (P : Measure (VaguePointMeasure ℝ)) with hμ
  have hNm : Measurable (fun ξ : VaguePointMeasure ℝ => ξ.measure (Ioo a b)) :=
    BlockBand.Counting.measurable_vague_Ioo_mass a b
  set E := {ξ : VaguePointMeasure ℝ | 2 ≤ ξ.measure (Ioo a b)} with hE
  set Z := {ξ : VaguePointMeasure ℝ | ξ.measure (Ioo a b) = 0} with hZ
  have hEm : MeasurableSet E := measurableSet_le measurable_const hNm
  have hZm : MeasurableSet Z := hNm (measurableSet_singleton 0)
  have hpt (ξ : VaguePointMeasure ℝ) :
      E.indicator 1 ξ + 1 ≤ ξ.measure (Ioo a b) + Z.indicator 1 ξ := by
    rcases ξ.integer_valued (Ioo a b) measurableSet_Ioo with h | ⟨m, h⟩
    · rw [h, top_add]; exact le_top
    · rcases m with _ | _ | m
      · have hE' : ξ ∉ E := by simp [hE, h]
        have hZ' : ξ ∈ Z := by simp [hZ, h]
        rw [indicator_of_notMem hE', indicator_of_mem hZ', h]
        simp
      · have hE' : ξ ∉ E := by
          simp only [hE, mem_ofPred_eq, h, not_le]
          norm_num
        have hZ' : ξ ∉ Z := by simp [hZ, h]
        rw [indicator_of_notMem hE', indicator_of_notMem hZ', h]
        simp
      · have hE' : ξ ∈ E := by
          simp only [hE, mem_ofPred_eq, h]
          exact_mod_cast (by omega : 2 ≤ m + 1 + 1)
        have hZ' : ξ ∉ Z := by simp [hZ, h]
        rw [indicator_of_mem hE', indicator_of_notMem hZ', h, Pi.one_apply, add_zero]
        have : ((2 : ℕ) : ℝ≥0∞) ≤ ((m + 1 + 1 : ℕ) : ℝ≥0∞) := by exact_mod_cast (by omega)
        calc (1 : ℝ≥0∞) + 1 = ((2 : ℕ) : ℝ≥0∞) := by norm_num
          _ ≤ _ := this
  have hint := lintegral_mono hpt (μ := μ)
  rw [lintegral_add_right _ measurable_const, lintegral_indicator_one hEm, lintegral_const,
    measure_univ, mul_one, lintegral_add_right _ (measurable_one.indicator hZm),
    lintegral_indicator_one hZm] at hint
  have h1 := lintegral_mass_Ioo_le_of_sineLaplace P hdetS hLap a b hab
  have h2 := measure_mass_Ioo_eq_zero_le_of_sineLaplace P hdetS hLap a b hab hb1
  have hδ0 : 0 ≤ b - a := sub_nonneg.2 hab
  have hsum : ENNReal.ofReal (b - a) + ENNReal.ofReal (1 - (b - a) + 3 * (b - a) ^ 3) =
      ENNReal.ofReal (3 * (b - a) ^ 3) + 1 := by
    rw [← ENNReal.ofReal_add hδ0 (by nlinarith [pow_nonneg hδ0 3]), ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_add (by positivity) zero_le_one]
    congr 1
    ring
  have := hint.trans (add_le_add h1 h2)
  rw [hsum] at this
  exact (ENNReal.add_le_add_iff_right ENNReal.one_ne_top).1 this

/-- **Simplicity from the sine Laplace functional.** Let `P` be a law on
locally finite point measures on `ℝ` (vague Borel σ-algebra) such that for
every nonnegative `f ∈ C_c(ℝ)`, `E_P exp (-ξ(f)) = sineLaplaceFunctional f`,
and assume the sine Gram determinants are bounded by one in absolute value.
Then `P`-almost every `ξ` is simple: `ξ {x} ≤ 1` for every `x : ℝ`. -/
theorem ae_isSimple_of_sineLaplace (P : ProbabilityMeasure (VaguePointMeasure ℝ))
    (hdetS : ∀ (k : ℕ) (x : Fin k → ℝ),
      |Matrix.det (fun i j : Fin k => sineKernel (x i) (x j))| ≤ 1)
    (hLap : ∀ f : CompactlySupportedContinuousMap ℝ ℝ, (∀ x, 0 ≤ f x) →
      ∫ ξ, Real.exp (-∫ x, f x ∂ξ.measure) ∂(P : Measure (VaguePointMeasure ℝ)) =
        sineLaplaceFunctional f) :
    ∀ᵐ ξ ∂(P : Measure (VaguePointMeasure ℝ)), IsSimplePointMeasure ξ := by
  set μ : Measure (VaguePointMeasure ℝ) := (P : Measure (VaguePointMeasure ℝ)) with hμ
  set w : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 2) with hw
  have hwpos (m : ℕ) : 0 < w m := by simp only [hw]; positivity
  have hwhalf (m : ℕ) : 2 * w m ≤ 1 := by
    simp only [hw]
    rw [← mul_div_assoc, mul_one, div_le_one (by positivity)]
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  set lo : ℕ → ℕ → ℕ → ℝ := fun L m i => -(L : ℝ) + ((i : ℝ) - 1) * w m with hlo
  set E : ℕ → ℕ → ℕ → Set (VaguePointMeasure ℝ) :=
    fun L m i => {ξ | 2 ≤ ξ.measure (Ioo (lo L m i) (lo L m i + 2 * w m))} with hE
  set cnt : ℕ → ℕ → ℕ := fun L m => 2 * L * (m + 2) + 1 with hcnt
  have hsub : {ξ | ¬ IsSimplePointMeasure ξ} ⊆
      ⋃ L : ℕ, ⋂ m : ℕ, ⋃ i ∈ Finset.range (cnt L m), E L m i := by
    intro ξ hξ
    simp only [IsSimplePointMeasure, not_forall, not_le, mem_ofPred_eq] at hξ
    obtain ⟨x, hx⟩ := hξ
    have h2 : 2 ≤ ξ.measure {x} := by
      rcases ξ.integer_valued {x} (measurableSet_singleton x) with h | ⟨k, h⟩
      · rw [h]; exact le_top
      · rw [h] at hx ⊢
        have hk : 1 < k := by exact_mod_cast hx
        have : ((2 : ℕ) : ℝ≥0∞) ≤ (k : ℝ≥0∞) := by exact_mod_cast hk
        simpa using this
    simp only [mem_iUnion, mem_iInter]
    refine ⟨⌈|x|⌉₊, fun m => ?_⟩
    set L := ⌈|x|⌉₊ with hL
    have hxL : |x| ≤ L := Nat.le_ceil _
    have hx0 : 0 ≤ x + L := by linarith [neg_abs_le x]
    have hx1 : x ≤ L := (le_abs_self x).trans hxL
    have hwm := hwpos m
    set i := ⌊(x + L) / w m⌋₊ with hi
    have hdiv : (x + L) / w m = (x + L) * ((m : ℝ) + 2) := by simp only [hw]; rw [div_div_eq_mul_div, div_one]
    have hi1 : (i : ℝ) * w m ≤ x + L := by
      have := Nat.floor_le (div_nonneg hx0 hwm.le)
      rwa [le_div_iff₀ hwm] at this
    have hi2 : x + L < ((i : ℝ) + 1) * w m := by
      have := Nat.lt_floor_add_one ((x + L) / w m)
      rwa [div_lt_iff₀ hwm] at this
    refine ⟨i, ?_, ?_⟩
    · rw [Finset.mem_range]
      have hle : (i : ℝ) ≤ 2 * L * ((m : ℝ) + 2) := by
        refine (Nat.floor_le (div_nonneg hx0 hwm.le)).trans ?_
        rw [hdiv]
        exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have : (i : ℝ) < ((2 * L * (m + 2) + 1 : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    · show 2 ≤ ξ.measure (Ioo (lo L m i) (lo L m i + 2 * w m))
      refine h2.trans (measure_mono (singleton_subset_iff.2 ⟨?_, ?_⟩))
      · simp only [hlo]; nlinarith
      · simp only [hlo]; nlinarith
  have hbound (L m : ℕ) : μ (⋂ m' : ℕ, ⋃ i ∈ Finset.range (cnt L m'), E L m' i) ≤
      ENNReal.ofReal ((cnt L m : ℝ) * (3 * (2 * w m) ^ 3)) := by
    refine (measure_mono (iInter_subset _ m)).trans ((measure_biUnion_finset_le _ _).trans ?_)
    calc ∑ i ∈ Finset.range (cnt L m), μ (E L m i)
          ≤ ∑ _i ∈ Finset.range (cnt L m), ENNReal.ofReal (3 * (2 * w m) ^ 3) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have := measure_two_le_mass_Ioo_le_of_sineLaplace P hdetS hLap (lo L m i)
            (lo L m i + 2 * w m) (by linarith [hwpos m]) (by linarith [hwhalf m])
          rwa [add_sub_cancel_left] at this
      _ = _ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  have hw0 : Tendsto w atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have htend (L : ℕ) : Tendsto (fun m : ℕ => (cnt L m : ℝ) * (3 * (2 * w m) ^ 3)) atTop
      (𝓝 0) := by
    have heq : (fun m : ℕ => (cnt L m : ℝ) * (3 * (2 * w m) ^ 3)) =
        fun m => 24 * (2 * L * w m ^ 2 + w m ^ 3) := by
      funext m
      have hm : (m : ℝ) + 2 ≠ 0 := by positivity
      simp only [hcnt, hw]
      push_cast
      field_simp
      ring
    rw [heq]
    simpa using (((hw0.pow 2).const_mul (2 * (L : ℝ))).add (hw0.pow 3)).const_mul 24
  rw [ae_iff]
  refine measure_mono_null hsub (measure_iUnion_null fun L => ?_)
  refine nonpos_iff_eq_zero.1 ?_
  have := ENNReal.tendsto_ofReal (htend L)
  rw [ENNReal.ofReal_zero] at this
  exact ge_of_tendsto' this (hbound L)

end BlockBand.Endpoints
