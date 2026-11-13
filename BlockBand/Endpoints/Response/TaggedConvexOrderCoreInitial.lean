module

public import BlockBand.Endpoints.Response.TaggedConvexOrderCoreGauss
public import BlockBand.Endpoints.Response.TaggedConvexOrderLimit

/-!
# Moments along a tagged sequence and the initial value

Law: `probedClockLaw W b`; `tcc_law` is the law on `ℝ` of `Z_{l;k} = W⁻¹h*Y_{l;k}h`. The birth
index `k` corresponds to block `k + 1`, and the birth length is `k + 1`. This file defines the
moment hypothesis `TccMomentsAlong` and the initial value `TccBirthAlong`, proves the moment bound
at fixed energy from `FullSourceMomentsContract`, and proves moment convergence from `L²`
concentration.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Filter Topology Polynomial Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal NNReal ComplexOrder

/-- The law on `ℝ` of `Z_{l;k}` at energy `e`. -/
def tcc_law (b e : ℝ) (W l k : ℕ) : Measure ℝ :=
  (probedClockLaw W b).map (lmf_tagResponseClock b e W l k)

theorem tcc_law_prob (b e : ℝ) (W l k : ℕ) : IsProbabilityMeasure (tcc_law b e W l k) := by
  have := tco_isProbabilityMeasure_probedClockLaw W b
  exact (Measure.isProbabilityMeasure_map_iff (tco_measurable_tagClock b e W l k).aemeasurable).2
    inferInstance

theorem tcc_psi_eq (b e : ℝ) (W l k : ℕ) (ψ : ℝ[X]) :
    tcc_psi b e W l k ψ = ∫ x, ψ.eval x ∂tcc_law b e W l k := by
  unfold tcc_psi tcc_law
  rw [integral_map (tco_measurable_tagClock b e W l k).aemeasurable
    (Polynomial.continuous ψ).aestronglyMeasurable]

theorem tcc_lintegral_law (b e : ℝ) (W l k : ℕ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂tcc_law b e W l k =
      ∫⁻ ω, ∫⁻ h, f (lmf_tagResponseClock b e W l k (ω, h))
        ∂circularVectorLaw (Fin 2 × Fin W) ∂growthPathLaw W b := by
  unfold tcc_law
  rw [lintegral_map hf (tco_measurable_tagClock b e W l k)]
  unfold probedClockLaw
  exact lintegral_prod _ (hf.comp (tco_measurable_tagClock b e W l k)).aemeasurable

/-- Moments along a tagged sequence: for every `m`, `E Z_{l;k}^{2m} ≤ C_m` eventually in `j`,
uniformly in the lengths `k_j < l ≤ n_j` (the full tag clock moments). -/
def TccMomentsAlong (b : ℝ) {s τ E : ℝ} (σ : TcoTagSequence s τ E) : Prop :=
  ∀ m : ℕ, ∃ C : ℝ, ∀ᶠ j in atTop, ∀ l, σ.k j < l → l ≤ σ.n j →
    ∫⁻ x, ENNReal.ofReal (x ^ (2 * m)) ∂tcc_law b (σ.energy j) (σ.W j) l (σ.k j) ≤
      ENNReal.ofReal C

/-- The initial value along a tagged sequence: every fixed moment of `Z_{k+1;k}` at the birth
length converges to `d^m`. -/
def TccBirthAlong (b : ℝ) {s τ E : ℝ} (σ : TcoTagSequence s τ E) : Prop :=
  ∀ m : ℕ, Tendsto (fun j => ∫ x, x ^ m ∂tcc_law b (σ.energy j) (σ.W j) (σ.k j + 1) (σ.k j))
    atTop (𝓝 (dStar b ^ m))

/-!
## Moments from the fixed-energy contract
-/

/-- `E Z_{n;k}^m ≤ C` at the fixed energy `E` from `FullSourceMomentsContract.tag`, uniformly in
`k < n ≤ TW` (fixed-energy analogue of `tco_tag_pow_bound`). -/
theorem tcc_tag_pow_bound_fixed (hMom : FullSourceMomentsContract) {b : ℝ}
    (hb : 0 < b) (hb' : b < 1 / 2) {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) (T : ℝ) {m : ℕ}
    (hm : 1 ≤ m) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ n : ℕ,
      (n : ℝ) ≤ T * W → ∀ k : ℕ, k < n →
        ∫⁻ x, ENNReal.ofReal (lmf_tagResponseClock b E W n k x ^ m) ∂probedClockLaw W b ≤
          ENNReal.ofReal C := by
  obtain ⟨c, hc0, hc⟩ := tco_lintegral_quadForm_pow_le m
  obtain ⟨Ct, W₀, hCt⟩ := hMom.tag b hb hb' E hE1 hE2 T m (by exact_mod_cast hm)
  set C' : ℝ := max Ct 0
  refine ⟨c * C' ^ m, W₀, by positivity, ?_⟩
  intro W hW n hn k hk
  have hprob := tco_isProbabilityMeasure_circularVectorLaw (ι := Fin 2 × Fin W)
  have hgp := tco_isProbabilityMeasure_growthPathLaw W b
  have hmeas := tco_measurable_tagClock b E W n k
  have hTr := hCt W hW n hn k hk
  set f : GrowthPath W → ℂ := fun ω => (W : ℂ)⁻¹ * (tagResponse b E W n k ω).trace
  have htr : ∀ ω, ENNReal.ofReal ((tco_tagQ b E W n k ω).trace.re) ≤ ‖f ω‖ₑ := by
    intro ω
    have e1 : (tco_tagQ b E W n k ω).trace.re = (f ω).re := by
      simp only [tco_tagQ, f, trace_smul, Complex.real_smul, Complex.mul_re, Complex.inv_re,
        Complex.inv_im, Complex.natCast_re, Complex.natCast_im]
      push_cast
      simp
    rw [e1, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (Complex.re_le_norm _)
  have hfm : AEStronglyMeasurable f (growthPathLaw W b) := by
    refine (Measurable.aestronglyMeasurable ?_)
    exact measurable_const.mul (Continuous.measurable (continuous_id.matrix_trace) |>.comp
      (tco_measurable_tagResponse b E W n k))
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hLm : ∫⁻ ω, ‖f ω‖ₑ ^ (m : ℝ) ∂growthPathLaw W b ≤ ENNReal.ofReal C' ^ (m : ℝ) := by
    rw [lintegral_rpow_enorm_eq_rpow_eLpNorm' hmpos]
    have h1 : eLpNorm f (ENNReal.ofReal (m : ℝ)) (growthPathLaw W b) =
        eLpNorm' f (m : ℝ) (growthPathLaw W b) := by
      rw [eLpNorm_eq_eLpNorm' (ENNReal.ofReal_pos.2 hmpos).ne' ENNReal.ofReal_ne_top hfm,
        ENNReal.toReal_ofReal hmpos.le]
    rw [← h1]
    exact ENNReal.rpow_le_rpow (hTr.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
      hmpos.le
  calc ∫⁻ x, ENNReal.ofReal (lmf_tagResponseClock b E W n k x ^ m) ∂probedClockLaw W b
      = ∫⁻ ω, ∫⁻ h, ENNReal.ofReal (lmf_tagResponseClock b E W n k (ω, h) ^ m)
          ∂circularVectorLaw (Fin 2 × Fin W) ∂growthPathLaw W b := by
        unfold probedClockLaw
        exact lintegral_prod _
          (ENNReal.measurable_ofReal.comp (hmeas.pow_const m)).aemeasurable
    _ ≤ ∫⁻ ω, ENNReal.ofReal (c * (tco_tagQ b E W n k ω).trace.re ^ m) ∂growthPathLaw W b := by
        refine lintegral_mono fun ω => ?_
        simp_rw [tco_tagClock_eq_quadForm]
        exact hc (Fin 2 × Fin W) _ (tco_posSemidef_tagQ b E W n k ω)
    _ ≤ ∫⁻ ω, ENNReal.ofReal c * ‖f ω‖ₑ ^ (m : ℝ) ∂growthPathLaw W b := by
        refine lintegral_mono fun ω => ?_
        rw [ENNReal.ofReal_mul hc0, ENNReal.ofReal_pow (tco_trace_tagQ_nonneg b E W n k ω),
          ← ENNReal.rpow_natCast]
        gcongr
        exact htr ω
    _ = ENNReal.ofReal c * ∫⁻ ω, ‖f ω‖ₑ ^ (m : ℝ) ∂growthPathLaw W b :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal c * ENNReal.ofReal C' ^ (m : ℝ) := by gcongr
    _ = ENNReal.ofReal (c * C' ^ m) := by
        rw [ENNReal.rpow_natCast, ← ENNReal.ofReal_pow (le_max_right _ _),
          ← ENNReal.ofReal_mul hc0]

/-- Eventually `W_j ≥ W₀` and `n_j ≤ (τ + 1) W_j`. -/
theorem tcc_eventually_len {s τ E : ℝ} (σ : TcoTagSequence s τ E) (W₀ : ℕ) :
    ∀ᶠ j in atTop, W₀ ≤ σ.W j ∧ (σ.n j : ℝ) ≤ (τ + 1) * σ.W j := by
  have h1 := σ.width_tendsto.eventually_ge_atTop W₀
  have h2 := σ.ratio_tendsto.eventually (gt_mem_nhds (show τ < τ + 1 by linarith))
  filter_upwards [h1, h2] with j hj1 hj2
  refine ⟨hj1, ?_⟩
  have hW : (0 : ℝ) < σ.W j := by exact_mod_cast σ.W_pos j
  rw [div_lt_iff₀ hW] at hj2
  exact hj2.le

/-- **`TccMomentsAlong` at constant energy** from the `FullSourceMomentsContract`. -/
theorem tcc_momentsAlong_fixed (hMom : FullSourceMomentsContract) {b : ℝ} (hb : 0 < b)
    (hb' : b < 1 / 2) {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) {s τ : ℝ}
    (σ : TcoTagSequence s τ E) (hσ : ∀ j, σ.energy j = E) : TccMomentsAlong b σ := by
  intro m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨1, Eventually.of_forall fun j l _ _ => ?_⟩
    have := tcc_law_prob b (σ.energy j) (σ.W j) l (σ.k j)
    simp
  obtain ⟨C, W₀, -, hC⟩ := tcc_tag_pow_bound_fixed hMom hb hb' hE1 hE2 (τ + 1)
    (m := 2 * m) (by omega)
  refine ⟨C, ?_⟩
  filter_upwards [tcc_eventually_len σ W₀] with j ⟨hW, hn⟩ l hkl hln
  unfold tcc_law
  rw [lintegral_map (by fun_prop : Measurable fun x : ℝ => ENNReal.ofReal (x ^ (2 * m)))
    (tco_measurable_tagClock _ _ _ _ _), hσ j]
  exact hC (σ.W j) hW l (le_trans (by exact_mod_cast hln) hn) (σ.k j) hkl

/-!
## The initial value
-/

/-- `|x^{r+1} - d^{r+1}| ≤ ((r+1)/2)(η⁻¹(x-d)² + η 4^r(x^{2r} + d^{2r}))` for `η > 0`. -/
theorem tcc_pow_sub_le (x d : ℝ) (r : ℕ) {η : ℝ} (hη : 0 < η) :
    |x ^ (r + 1) - d ^ (r + 1)| ≤
      ((r : ℝ) + 1) / 2 * (η⁻¹ * (x - d) ^ 2 + η * (4 ^ r * (x ^ (2 * r) + d ^ (2 * r)))) := by
  set S := |x| + |d|
  have hS : 0 ≤ S := by positivity
  have hgeo : |∑ i ∈ Finset.range (r + 1), x ^ i * d ^ (r + 1 - 1 - i)| ≤ ((r : ℝ) + 1) * S ^ r := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hb : ∀ i ∈ Finset.range (r + 1), |x ^ i * d ^ (r + 1 - 1 - i)| ≤ S ^ r := by
      intro i hi
      have hi' : i ≤ r := by simp at hi; omega
      rw [abs_mul, abs_pow, abs_pow]
      calc |x| ^ i * |d| ^ (r + 1 - 1 - i) ≤ S ^ i * S ^ (r + 1 - 1 - i) := by
            gcongr
            · exact le_add_of_nonneg_right (abs_nonneg d)
            · exact le_add_of_nonneg_left (abs_nonneg x)
        _ = S ^ r := by rw [← pow_add]; congr 1; omega
    refine (Finset.sum_le_sum hb).trans ?_
    simp
  have hfac : x ^ (r + 1) - d ^ (r + 1) =
      (∑ i ∈ Finset.range (r + 1), x ^ i * d ^ (r + 1 - 1 - i)) * (x - d) :=
    (geom_sum₂_mul x d (r + 1)).symm
  have hS2 : S ^ (2 * r) ≤ 4 ^ r * (x ^ (2 * r) + d ^ (2 * r)) := by
    have h := tco_add_pow_le |x| |d| (abs_nonneg x) (abs_nonneg d) (2 * r)
    rw [pow_mul (2 : ℝ), show (2 : ℝ) ^ 2 = 4 by norm_num, (even_two_mul r).pow_abs,
      (even_two_mul r).pow_abs] at h
    exact h
  have hamgm : |x - d| * S ^ r ≤ (η⁻¹ * (x - d) ^ 2 + η * S ^ (2 * r)) / 2 := by
    have h0 : 0 ≤ (|x - d| - η * S ^ r) ^ 2 := sq_nonneg _
    have e1 : (x - d) ^ 2 = |x - d| ^ 2 := (sq_abs _).symm
    have e2 : S ^ (2 * r) = (S ^ r) ^ 2 := by rw [← pow_mul, mul_comm]
    rw [e1, e2]
    have hηi : η⁻¹ * η = 1 := inv_mul_cancel₀ hη.ne'
    have key : η⁻¹ * |x - d| ^ 2 + η * (S ^ r) ^ 2 - 2 * (|x - d| * S ^ r) =
        η⁻¹ * (|x - d| - η * S ^ r) ^ 2 := by
      have : η⁻¹ * (|x - d| - η * S ^ r) ^ 2 =
          η⁻¹ * |x - d| ^ 2 - 2 * (η⁻¹ * η) * (|x - d| * S ^ r) +
            (η⁻¹ * η) * (η * (S ^ r) ^ 2) := by ring
      rw [this, hηi]; ring
    have : 0 ≤ η⁻¹ * (|x - d| - η * S ^ r) ^ 2 := mul_nonneg (inv_nonneg.2 hη.le) h0
    linarith
  rw [hfac, abs_mul]
  have hr : (0 : ℝ) ≤ (r : ℝ) + 1 := by positivity
  calc |∑ i ∈ Finset.range (r + 1), x ^ i * d ^ (r + 1 - 1 - i)| * |x - d|
      ≤ ((r : ℝ) + 1) * S ^ r * |x - d| := by gcongr
    _ = ((r : ℝ) + 1) * (|x - d| * S ^ r) := by ring
    _ ≤ ((r : ℝ) + 1) * ((η⁻¹ * (x - d) ^ 2 + η * S ^ (2 * r)) / 2) := by gcongr
    _ ≤ ((r : ℝ) + 1) * ((η⁻¹ * (x - d) ^ 2 + η * (4 ^ r * (x ^ (2 * r) + d ^ (2 * r)))) / 2) := by
        gcongr
    _ = _ := by ring

theorem tcc_integral_le_of_lintegral {μ : Measure ℝ} {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x)
    (hfm : AEStronglyMeasurable f μ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ ENNReal.ofReal C) : ∫ x, f x ∂μ ≤ C := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf0) hfm]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hC).trans (ENNReal.toReal_ofReal hC0).le

/-- Moment convergence from `L²` concentration (generic form): if `μ_j` are probability measures
on `ℝ` with bounded fixed moments and `E(x - d)² → 0`, every fixed moment converges to `d^m`. -/
theorem tcc_moment_tendsto_of_sq {μ : ℕ → Measure ℝ} (hμ : ∀ j, IsProbabilityMeasure (μ j))
    (d : ℝ) (hmom : ∀ m : ℕ, ∃ C : ℝ, ∀ᶠ j in atTop,
      ∫⁻ x, ENNReal.ofReal (x ^ (2 * m)) ∂μ j ≤ ENNReal.ofReal C)
    (hsq : ∀ θ : ℝ, 0 < θ → ∀ᶠ j in atTop, ∫⁻ x, ENNReal.ofReal ((x - d) ^ 2) ∂μ j ≤
      ENNReal.ofReal θ) (m : ℕ) :
    Tendsto (fun j => ∫ x, x ^ m ∂μ j) atTop (𝓝 (d ^ m)) := by
  rcases m with _ | r
  · simp only [pow_zero, integral_const, smul_eq_mul, mul_one]
    have : ∀ j, (μ j).real Set.univ = 1 := fun j => by simp [measureReal_def]
    simp_rw [this]
    exact tendsto_const_nhds
  obtain ⟨Cm, hCm⟩ := hmom (r + 1)
  obtain ⟨C0, hC0⟩ := hmom r
  obtain ⟨C1, hC1⟩ := hmom 1
  set C0' := max C0 0
  set A : ℝ := ((r : ℝ) + 1) / 2
  have hA : 0 < A := by positivity
  set K : ℝ := 4 ^ r * (C0' + d ^ (2 * r))
  have hK : 0 ≤ K := by
    have : 0 ≤ d ^ (2 * r) := by rw [pow_mul]; positivity
    have : 0 ≤ C0' := le_max_right _ _
    positivity
  rw [Metric.tendsto_nhds]
  intro ε hε
  set η : ℝ := ε / (2 * (A * K + 1))
  have hη : 0 < η := by positivity
  set θ : ℝ := ε * η / (4 * A)
  have hθ : 0 < θ := by positivity
  filter_upwards [hsq θ hθ, hCm, hC0, hC1] with j hj hjm hj0 hj1
  have := hμ j
  have hevn : ∀ (q : ℕ) (x : ℝ), 0 ≤ x ^ (2 * q) := fun q x => by rw [pow_mul]; positivity
  obtain ⟨-, im⟩ := tco_integrable_of_lintegral_pow (r + 1) hjm
  obtain ⟨i0, -⟩ := tco_integrable_of_lintegral_pow r hj0
  obtain ⟨i2, i1⟩ := tco_integrable_of_lintegral_pow 1 hj1
  have isq : Integrable (fun x : ℝ => (x - d) ^ 2) (μ j) := by
    have e : (fun x : ℝ => (x - d) ^ 2) = fun x => x ^ (2 * 1) - 2 * d * x ^ 1 + d ^ 2 := by
      funext x; ring
    rw [e]; exact (i2.sub (i1.const_mul _)).add (integrable_const _)
  have hsqle : ∫ x, (x - d) ^ 2 ∂μ j ≤ θ :=
    tcc_integral_le_of_lintegral (fun x => sq_nonneg _) (by fun_prop) hθ.le hj
  have h0le : ∫ x, x ^ (2 * r) ∂μ j ≤ C0' :=
    tcc_integral_le_of_lintegral (hevn r) (by fun_prop) (le_max_right _ _)
      (hj0.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  have irhs : Integrable (fun x : ℝ => A * (η⁻¹ * (x - d) ^ 2 +
      η * (4 ^ r * (x ^ (2 * r) + d ^ (2 * r))))) (μ j) :=
    ((isq.const_mul _).add (((i0.add (integrable_const _)).const_mul _).const_mul _)).const_mul _
  have hdiff : ∫ x, x ^ (r + 1) ∂μ j - d ^ (r + 1) = ∫ x, (x ^ (r + 1) - d ^ (r + 1)) ∂μ j := by
    rw [integral_sub im (integrable_const _), integral_const]; simp [measureReal_def]
  rw [Real.dist_eq, hdiff]
  refine (abs_integral_le_integral_abs).trans_lt ?_
  refine (integral_mono (im.sub (integrable_const _)).abs irhs fun x =>
    tcc_pow_sub_le x d r hη).trans_lt ?_
  have j0 : Integrable (fun x : ℝ => x ^ (2 * r) + d ^ (2 * r)) (μ j) := i0.add (integrable_const _)
  have ja : Integrable (fun x : ℝ => η⁻¹ * (x - d) ^ 2) (μ j) := isq.const_mul _
  have jb : Integrable (fun x : ℝ => η * (4 ^ r * (x ^ (2 * r) + d ^ (2 * r)))) (μ j) :=
    (j0.const_mul _).const_mul _
  rw [integral_const_mul, integral_add ja jb, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_add i0 (integrable_const _), integral_const]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  have h1 : A * (η⁻¹ * ∫ x, (x - d) ^ 2 ∂μ j) ≤ ε / 4 := by
    calc A * (η⁻¹ * ∫ x, (x - d) ^ 2 ∂μ j) ≤ A * (η⁻¹ * θ) := by gcongr
      _ = ε / 4 := by
          simp only [θ]; field_simp
  have h2 : A * (η * (4 ^ r * (∫ x, x ^ (2 * r) ∂μ j + d ^ (2 * r)))) ≤ A * η * K := by
    have : A * (η * (4 ^ r * (∫ x, x ^ (2 * r) ∂μ j + d ^ (2 * r)))) =
        A * η * (4 ^ r * (∫ x, x ^ (2 * r) ∂μ j + d ^ (2 * r))) := by ring
    rw [this]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    simp only [K]
    gcongr
  have h3 : A * η * K < ε / 2 := by
    have hden : 0 < 2 * (A * K + 1) := by positivity
    have e : A * η * K = ε * (A * K) / (2 * (A * K + 1)) := by simp only [η]; ring
    rw [e, div_lt_iff₀ hden]
    nlinarith
  rw [mul_add]
  linarith

/-- **`E(Z_{k+1;k} - d)² → 0` at constant energy**, from
`TagBirthValueContract` (`trace` at `p = 2`, `square`) and
`E_h(h*Qh - d)² = (Tr Q - d)² + Tr Q²`.
-/
theorem tcc_birth_sq_fixed (hBirth : TagBirthValueContract) {b : ℝ} (hb : 0 < b)
    (hb' : b < 1 / 2) {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) {s τ : ℝ} (hs : 0 < s)
    (σ : TcoTagSequence s τ E) (hσ : ∀ j, σ.energy j = E) (θ : ℝ) (hθ : 0 < θ) :
    ∀ᶠ j in atTop, ∫⁻ x, ENNReal.ofReal ((x - dStar b) ^ 2)
      ∂tcc_law b (σ.energy j) (σ.W j) (σ.k j + 1) (σ.k j) ≤ ENNReal.ofReal θ := by
  have hsτ := tco_tagSequence_s_le σ
  set ε := s / 2
  set T := τ + 1
  have hε : 0 < ε := by positivity
  have hεT : ε < T := by simp only [ε, T]; linarith
  set θ' := Real.sqrt (θ / 2)
  have hθ' : 0 < θ' := Real.sqrt_pos.2 (by positivity)
  obtain ⟨W₁, hW₁⟩ := hBirth.trace b hb hb' E hE1 hE2 ε T 2 hε hεT (by norm_num) θ' hθ'
  obtain ⟨C, W₂, hW₂⟩ := hBirth.square b hb hb' E hE1 hE2 ε T hε hεT
  have hCW : Tendsto (fun j => C / (σ.W j : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat C).comp σ.width_tendsto
  have hk := σ.tag_tendsto.eventually (lt_mem_nhds (show ε < s by simp only [ε]; linarith))
  filter_upwards [tcc_eventually_len σ (max W₁ W₂), hk,
    hCW.eventually (gt_mem_nhds (show (0 : ℝ) < θ / 2 by positivity))] with j ⟨hWj, hn⟩ hkj hCj
  set W := σ.W j
  set k := σ.k j
  have hW0 : (0 : ℝ) < W := by exact_mod_cast σ.W_pos j
  have hεk : ε * W ≤ k := by rw [lt_div_iff₀ hW0] at hkj; exact hkj.le
  have hkT : ((k + 1 : ℕ) : ℝ) ≤ T * W :=
    le_trans (by exact_mod_cast σ.tag_lt j) hn
  have htr := hW₁ W (le_trans (le_max_left _ _) hWj) k hεk hkT
  have hsqr := hW₂ W (le_trans (le_max_right _ _) hWj) k hεk hkT
  rw [hσ j]
  set f : GrowthPath W → ℂ := fun ω => (W : ℂ)⁻¹ * (tagResponse b E W (k + 1) k ω).trace -
    (dStar b : ℂ)
  set g : GrowthPath W → ℂ := fun ω => (((W : ℂ)⁻¹ • tagResponse b E W (k + 1) k ω) ^ 2).trace
  have hQ : ∀ ω, (W : ℂ)⁻¹ • tagResponse b E W (k + 1) k ω = tco_tagQ b E W (k + 1) k ω := by
    intro ω; unfold tco_tagQ; ext x y; simp [Complex.real_smul]
  have hpt : ∀ ω, ∫⁻ h, ENNReal.ofReal ((lmf_tagResponseClock b E W (k + 1) k (ω, h) -
      dStar b) ^ 2) ∂circularVectorLaw (Fin 2 × Fin W) ≤ ‖f ω‖ₑ ^ 2 + ‖g ω‖ₑ := by
    intro ω
    set B := tco_tagQ b E W (k + 1) k ω
    have hB : B.IsHermitian := (tco_posSemidef_tagQ b E W (k + 1) k ω).isHermitian
    obtain ⟨-, -, i2, e2⟩ := tcc_quadForm_centered hB (dStar b)
    simp_rw [tco_tagClock_eq_quadForm]
    rw [← ofReal_integral_eq_lintegral_ofReal i2 (ae_of_all _ fun _ => sq_nonneg _), e2,
      ← rvG_trace_re_eq hB]
    have e3 : ∑ i, hB.eigenvalues i ^ 2 = (g ω).re := by
      rw [← rvG_hsSq_eq hB, ← trace_conjTranspose_mul_self_re_eq_hsSq, hB.eq]
      simp only [g, hQ, pow_two]
      rfl
    have e4 : B.trace.re - dStar b = (f ω).re := by
      simp only [f, ← hQ ω, B, trace_smul, smul_eq_mul, Complex.sub_re]
      simp
    rw [e3, e4]
    calc ENNReal.ofReal ((f ω).re ^ 2 + (g ω).re)
        ≤ ENNReal.ofReal (‖f ω‖ ^ 2 + ‖g ω‖) := by
          refine ENNReal.ofReal_le_ofReal (add_le_add ?_ (Complex.re_le_norm _))
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2
      _ = ‖f ω‖ₑ ^ 2 + ‖g ω‖ₑ := by
          rw [ENNReal.ofReal_add (by positivity) (norm_nonneg _), ENNReal.ofReal_pow
            (norm_nonneg _), ofReal_norm, ofReal_norm]
  have hfm : Measurable f := by
    refine Measurable.sub ?_ measurable_const
    exact measurable_const.mul (Continuous.measurable (continuous_id.matrix_trace) |>.comp
      (tco_measurable_tagResponse b E W (k + 1) k))
  have hL2 : ∫⁻ ω, ‖f ω‖ₑ ^ 2 ∂growthPathLaw W b ≤ ENNReal.ofReal (θ / 2) := by
    have h2 : (0 : ℝ) < 2 := by norm_num
    have e : ∫⁻ ω, ‖f ω‖ₑ ^ 2 ∂growthPathLaw W b = ∫⁻ ω, ‖f ω‖ₑ ^ (2 : ℝ) ∂growthPathLaw W b := by
      simp_rw [← ENNReal.rpow_natCast]; norm_num
    rw [e, lintegral_rpow_enorm_eq_rpow_eLpNorm' h2]
    have h1 : eLpNorm f (ENNReal.ofReal 2) (growthPathLaw W b) =
        eLpNorm' f 2 (growthPathLaw W b) := by
      rw [eLpNorm_eq_eLpNorm' (ENNReal.ofReal_pos.2 h2).ne' ENNReal.ofReal_ne_top
        hfm.aestronglyMeasurable, ENNReal.toReal_ofReal h2.le]
    rw [← h1]
    calc eLpNorm f (ENNReal.ofReal 2) (growthPathLaw W b) ^ (2 : ℝ)
        ≤ ENNReal.ofReal θ' ^ (2 : ℝ) := ENNReal.rpow_le_rpow htr h2.le
      _ = ENNReal.ofReal (θ / 2) := by
          rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow hθ'.le, Real.sq_sqrt (by positivity)]
  rw [tcc_lintegral_law _ _ _ _ _ (by fun_prop)]
  calc ∫⁻ ω, ∫⁻ h, ENNReal.ofReal ((lmf_tagResponseClock b E W (k + 1) k (ω, h) - dStar b) ^ 2)
        ∂circularVectorLaw (Fin 2 × Fin W) ∂growthPathLaw W b
      ≤ ∫⁻ ω, (‖f ω‖ₑ ^ 2 + ‖g ω‖ₑ) ∂growthPathLaw W b := lintegral_mono hpt
    _ = ∫⁻ ω, ‖f ω‖ₑ ^ 2 ∂growthPathLaw W b + ∫⁻ ω, ‖g ω‖ₑ ∂growthPathLaw W b :=
        lintegral_add_left (hfm.enorm.pow_const 2) _
    _ ≤ ENNReal.ofReal (θ / 2) + ENNReal.ofReal (C / W) := add_le_add hL2 hsqr
    _ ≤ ENNReal.ofReal (θ / 2) + ENNReal.ofReal (max (C / W) 0) :=
        add_le_add le_rfl (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    _ = ENNReal.ofReal (θ / 2 + max (C / W) 0) :=
        (ENNReal.ofReal_add (by positivity) (le_max_right _ _)).symm
    _ ≤ ENNReal.ofReal θ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have := max_lt hCj (show (0 : ℝ) < θ / 2 by positivity)
        linarith

/-- **Step 5 at constant energy**: the initial value `TccBirthAlong`, from the
`TagBirthValueContract` and `FullSourceMomentsContract`.
-/
theorem tcc_birthAlong_fixed (hMom : FullSourceMomentsContract)
    (hBirth : TagBirthValueContract) {b : ℝ} (hb : 0 < b) (hb' : b < 1 / 2) {E : ℝ}
    (hE1 : -2 < E) (hE2 : E < 2) {s τ : ℝ} (hs : 0 < s) (σ : TcoTagSequence s τ E)
    (hσ : ∀ j, σ.energy j = E) : TccBirthAlong b σ := by
  have hM := tcc_momentsAlong_fixed hMom hb hb' hE1 hE2 σ hσ
  refine tcc_moment_tendsto_of_sq (fun j => tcc_law_prob _ _ _ _ _) (dStar b) (fun m => ?_)
    (tcc_birth_sq_fixed hBirth hb hb' hE1 hE2 hs σ hσ)
  obtain ⟨C, hC⟩ := hM m
  exact ⟨C, hC.mono fun j hj => hj _ (Nat.lt_succ_self _) (σ.tag_lt j)⟩

end BlockBand.Endpoints
