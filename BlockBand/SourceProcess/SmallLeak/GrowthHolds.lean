module

public import BlockBand.SourceProcess.SmallLeak.GrowthStop
public import BlockBand.SourceProcess.SmallLeak.Interface
public import BlockBand.SourceProcess.RawTag.DeltaBounds
public import BlockBand.SourceProcess.FullSource.TagLayer
public import BlockBand.SourceProcess.FullSource.Clock
public import BlockBand.SourceProcess.FullSource.Conversion
public import BlockBand.SourceProcess.FullSource.TagFinal
public import BlockBand.SourceProcess.FullSource.DeltaHolds
public import BlockBand.SourceProcess.TagBirth.Main

/-!
# Growth of the omitted flux

This file proves `OmittedFluxGrowth` from the Gaussian layer hypotheses and the scalar recursion.
Iterate `flux_stopped_step` from `n_s` (`k = n_s - 1`):
`E[1_{G_j}Z_j] ≤ e^{αT}(1 + Kd) E g_{n_s}`; off the δ-stop, `g_j ≤ W` and
`W·P(G_jᶜ) ≤ W⌊TW⌋e^{-cW log W} ≤ η` (`SuperexpExit`, `superexp_absorbs`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.SmallLeak

open MeasureTheory Filter Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.Bridge BlockBand.SourceProcess.Closing
open BlockBand.SourceProcess.FullSourceStops BlockBand.SourceProcess.FullSource
open BlockBand.Transmission.PathScalar BlockBand.Transmission.PassiveLayer
open BlockBand.SourceProcess.TagBirth BlockBand.SourceProcess.RawTag
open scoped ENNReal Matrix.Norms.L2Operator

variable {W : ℕ}

/-- The weight dominates the flux. -/
theorem ofReal_flux_le_weight {b E h s K : ℝ} (hK : 0 ≤ K) (j : ℕ) (ω : GrowthPath W) :
    ENNReal.ofReal (omittedFlux b E h s W j ω) ≤ fluxWeight b E h s K W j ω := by
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 := omittedFlux_nonneg b E h s W j ω
  have h2 : 0 ≤ pathDelta b E W j ω := norm_nonneg _
  nlinarith [mul_nonneg (mul_nonneg hK h2) h1]

/-- **`OmittedFluxGrowth`** from the input hypotheses. -/
theorem omittedFluxGrowth_holds (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) : OmittedFluxGrowth := by
  intro b hb0 hb E hE1 hE2 s T hs hsT
  obtain ⟨hκ, hEκ⟩ := mem_bulkInterval_self hE1 hE2
  set κ := min (E + 2) (2 - E)
  obtain ⟨Ca, C₂, Cn, CN₂, CN, Cf, Cm, ρ, d₀, WL, hCa, hC₂, hCn, hCN, hCf, hCm, hρ0, hρ1, hd₀,
    hL⟩ := tagLayerBounds_of (fullSourceEstimates_holds hGA hLp)
      (passiveMeanStep_holds (passiveBounds_holds hGA hLp)) (passiveFluctuationStep_holds hGA hLp)
      hb0 hb hκ (n := 2) le_rfl
  obtain ⟨Cm', Cf', W₂, hCm', hCf', hΔb⟩ := delta_fresh_bounds hGA hLp b hb0 hb κ hκ 2 (by norm_num)
  obtain ⟨CD, W₃, hCD, hΔ4⟩ := delta_moments hGA b hb0 hb κ hκ 4 (by norm_num)
  have hη : 0 < etaZ b E := boundaryZ_im_pos (by linarith) hE1 hE2
  set η := etaZ b E
  set La := Cm' / η
  have hLa : 0 ≤ La := div_nonneg hCm' hη.le
  set Kw := 2 * La / (1 - ρ)
  have hKw : 0 ≤ Kw := div_nonneg (by linarith) (by linarith)
  have hKL : La ≤ Kw * (1 - ρ) / 2 := by
    simp only [Kw]; rw [div_mul_cancel₀ _ (by linarith : (1 - ρ) ≠ 0)]; linarith
  set d := min (min d₀ 1) ((1 - ρ) / (2 * (ρ * La + 1)))
  have hden : 0 < 2 * (ρ * La + 1) := by nlinarith [mul_nonneg hρ0 hLa]
  have hd0 : 0 < d := lt_min (lt_min hd₀ one_pos) (div_pos (by linarith) hden)
  have hd1 : d ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hdd₀ : d ≤ d₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hρLd : ρ * La * d ≤ (1 - ρ) / 2 := by
    have h1 : d ≤ (1 - ρ) / (2 * (ρ * La + 1)) := min_le_right _ _
    have h2 : ρ * La * d ≤ ρ * La * ((1 - ρ) / (2 * (ρ * La + 1))) :=
      mul_le_mul_of_nonneg_left h1 (mul_nonneg hρ0 hLa)
    have h3 : ρ * La * ((1 - ρ) / (2 * (ρ * La + 1))) ≤ (1 - ρ) / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ hden (by norm_num)]
      nlinarith [mul_nonneg hρ0 hLa]
    linarith
  set α := alphaG Kw Cm La Cf ((1 + CD / (2 * η)) ^ 4)
  have hα : 0 ≤ α := alphaG_nonneg hKw hCm hLa (by positivity)
  refine ⟨Real.exp (α * T) * (1 + Kw * d), fun h h0 _ η' hη' => ?_⟩
  obtain ⟨c, Ws, hc, hSup⟩ := superexpExit_of hSR b hb0 hb κ T hκ d hd0
  obtain ⟨W₄, hW₄⟩ := superexp_absorbs (A := Real.exp 1) (B := 1 / η') (c := c) (T := T) (R := 1)
    (Real.one_le_exp zero_le_one) (by positivity) hc
  filter_upwards [eventually_ge_atTop (max (max (max WL W₂) (max W₃ Ws))
    (max W₄ (⌈1 / s⌉₊ + 1)))] with W hW j hj1 hj2
  have hWL : WL ≤ W := le_trans (by simp) hW
  have hW2 : W₂ ≤ W := le_trans (by simp) hW
  have hW3 : W₃ ≤ W := le_trans (by simp) hW
  have hWs : Ws ≤ W := le_trans (by simp) hW
  have hW4 : W₄ ≤ W := le_trans (by simp) hW
  have hWc : ⌈1 / s⌉₊ + 1 ≤ W := le_trans (by simp) hW
  have hW1 : 1 ≤ W := by omega
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  set μ := growthPathLaw W b
  set n := ⌊(W : ℝ) * s⌋₊
  have hn1 : 1 ≤ n := by
    refine Nat.le_floor ?_
    have : 1 / s ≤ W := (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈1 / s⌉₊ ≤ W))
    rw [div_le_iff₀ hs] at this
    push_cast; linarith
  set k := n - 1
  have hk : k + 1 = n := by omega
  set I : ℕ → ℝ≥0∞ := fun m =>
    ∫⁻ ω, (stopEv b E W k d m).indicator (fluxWeight b E h s Kw W m) ω ∂μ
  set q := ENNReal.ofReal (1 + α / W)
  have hstep : ∀ i, I (n + i + 1) ≤ q * I (n + i) := fun i =>
    flux_stopped_step (h := h) (s := s) hb0 hb hE1 hE2 hW1 (k := k) (j := n + i) (by omega)
      (by omega) (by omega) (hL W hWL E hEκ) (Cm' := Cm')
      (fun X hX => ⟨(hΔb W hW2 E hEκ X hX).1, (hΔb W hW2 E hEκ X hX).2.1⟩) hCD
      (fun X hX => by exact_mod_cast hΔ4 W hW3 E hEκ X hX) hCf hCm hKw hρ0 hρ1 hLa hKL hd1 hρLd
      hdd₀
  have hiter : ∀ i, I (n + i) ≤ q ^ i * I n := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      calc I (n + (i + 1)) = I (n + i + 1) := rfl
        _ ≤ q * I (n + i) := hstep i
        _ ≤ q * (q ^ i * I n) := mul_le_mul_right ih _
        _ = q ^ (i + 1) * I n := by ring
  -- the base
  have hbase : I n ≤ ENNReal.ofReal (1 + Kw * d) *
      ∫⁻ ω, ENNReal.ofReal (omittedFlux b E h s W n ω) ∂μ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun ω => ?_
    by_cases hG : ω ∈ stopEv b E W k d n
    · rw [Set.indicator_of_mem hG, fluxWeight, ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_
        (omittedFlux_nonneg _ _ _ _ _ _ _))
      have := hG n (by omega) le_rfl
      nlinarith
    · rw [Set.indicator_of_notMem hG]; exact zero_le
  -- the point `j`
  obtain ⟨i, rfl⟩ : ∃ i, j = n + i := ⟨j - n, by omega⟩
  have hjT : ((n + i : ℕ) : ℝ) ≤ T * W := by
    have hT0 : 0 ≤ T := by linarith
    have := Nat.floor_le (show 0 ≤ (W : ℝ) * T from mul_nonneg hW0.le hT0)
    have h' : ((n + i : ℕ) : ℝ) ≤ (⌊(W : ℝ) * T⌋₊ : ℝ) := by exact_mod_cast hj2
    linarith [mul_comm (W : ℝ) T]
  have hiT : (i : ℝ) ≤ T * W := by
    have : (i : ℝ) ≤ ((n + i : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left i n
    linarith
  have hq : q ^ i ≤ ENNReal.ofReal (Real.exp (α * T)) := by
    rw [← ENNReal.ofReal_pow (by have := hα; positivity)]
    exact ENNReal.ofReal_le_ofReal (one_add_pow_le_exp hα i hW0 hiT)
  -- the exit
  set G := stopEv b E W k d (n + i)
  have hGm : MeasurableSet G := measurableSet_stopEv b E k d _
  have hexit : ENNReal.ofReal W * μ Gᶜ ≤ ENNReal.ofReal η' := by
    have h1 := (measure_mono (stopEv_compl_subset b E k d T hjT)).trans (hSup W hWs E hEκ)
    have h2 := hW₄ W hW4 W (by simp)
    have hWe : (W : ℝ) ≤ Real.exp 1 ^ W := by
      rw [← Real.exp_nat_mul, mul_one]; linarith [Real.add_one_le_exp (W : ℝ)]
    set x := (⌊T * W⌋₊ : ℝ) * Real.exp (-(c * W * Real.log W))
    have hx : 0 ≤ x := by positivity
    have h3 : (W : ℝ) * x ≤ η' := by
      have : x * (Real.exp 1 ^ W * (1 / η')) ≤ 1 := h2
      have h4 : x * ((W : ℝ) * (1 / η')) ≤ 1 :=
        le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hWe (by positivity)) hx)
          this
      have e : x * ((W : ℝ) * (1 / η')) = W * x / η' := by ring
      rw [e, div_le_one hη'] at h4
      exact h4
    calc ENNReal.ofReal W * μ Gᶜ ≤ ENNReal.ofReal W * ENNReal.ofReal x := mul_le_mul_right h1 _
      _ = ENNReal.ofReal (W * x) := (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ ENNReal.ofReal η' := ENNReal.ofReal_le_ofReal h3
  have hoff : ∫⁻ ω, Gᶜ.indicator (fun ω => ENNReal.ofReal (omittedFlux b E h s W (n + i) ω)) ω ∂μ ≤
      ENNReal.ofReal W * μ Gᶜ := by
    calc _ ≤ ∫⁻ ω, Gᶜ.indicator (fun _ => ENNReal.ofReal W) ω ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_omittedFlux_le (h := h) (s := s) hb hE1 hE2 hW1 (n + i)] with ω hω
          by_cases hm : ω ∈ Gᶜ
          · simp only [Set.indicator_of_mem hm]; exact ENNReal.ofReal_le_ofReal hω
          · simp only [Set.indicator_of_notMem hm]; exact le_rfl
      _ = ENNReal.ofReal W * μ Gᶜ := lintegral_indicator_const hGm.compl _
  have hsplit : ∫⁻ ω, ENNReal.ofReal (omittedFlux b E h s W (n + i) ω) ∂μ ≤
      I (n + i) + ENNReal.ofReal W * μ Gᶜ := by
    refine le_trans ?_ (add_le_add le_rfl hoff)
    rw [← lintegral_add_left ((measurable_fluxWeight b E h s Kw _).indicator hGm)]
    refine lintegral_mono fun ω => ?_
    by_cases hm : ω ∈ G
    · simp only [Set.indicator_of_mem hm, Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hm),
        add_zero]
      exact ofReal_flux_le_weight hKw _ ω
    · simp only [Set.indicator_of_notMem hm, Set.indicator_of_mem (Set.mem_compl hm), zero_add]
      exact le_rfl
  -- integrability of `g_{n_s}`
  have hint : Integrable (fun ω => omittedFlux b E h s W n ω) μ := by
    refine Integrable.mono' (integrable_const (W : ℝ)) (measurable_omittedFlux b E h s n).aestronglyMeasurable ?_
    filter_upwards [ae_omittedFlux_le (h := h) (s := s) hb hE1 hE2 hW1 n] with ω hω
    rw [Real.norm_of_nonneg (omittedFlux_nonneg _ _ _ _ _ _ _)]; exact hω
  have hI0 : 0 ≤ ∫ ω, omittedFlux b E h s W n ω ∂μ :=
    integral_nonneg fun ω => omittedFlux_nonneg _ _ _ _ _ _ _
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (omittedFlux_nonneg b E h s W (n + i)))
    (measurable_omittedFlux b E h s (n + i)).aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  calc _ ≤ I (n + i) + ENNReal.ofReal W * μ Gᶜ := hsplit
    _ ≤ q ^ i * (ENNReal.ofReal (1 + Kw * d) * ENNReal.ofReal (∫ ω, omittedFlux b E h s W n ω ∂μ))
          + ENNReal.ofReal η' := by
        refine add_le_add ((hiter i).trans (mul_le_mul_right ?_ _)) hexit
        rw [ofReal_integral_eq_lintegral_ofReal hint
          (ae_of_all _ fun ω => omittedFlux_nonneg _ _ _ _ _ _ _)]
        exact hbase
    _ ≤ ENNReal.ofReal (Real.exp (α * T)) * (ENNReal.ofReal (1 + Kw * d) *
          ENNReal.ofReal (∫ ω, omittedFlux b E h s W n ω ∂μ)) + ENNReal.ofReal η' := by
        gcongr
    _ = ENNReal.ofReal (Real.exp (α * T) * (1 + Kw * d) * ∫ ω, omittedFlux b E h s W n ω ∂μ +
          η') := by
        rw [ENNReal.ofReal_add (by positivity) hη'.le, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by positivity), mul_assoc]

end BlockBand.SourceProcess.SmallLeak
