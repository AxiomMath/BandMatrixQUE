module

public import BlockBand.Endpoints.Response.ClockEntranceStepDefs
public import BlockBand.Endpoints.Response.EdgeClockMoments
public import BlockBand.Endpoints.Response.TaggedConvexOrderMoments
public import BlockBand.Endpoints.Poisson.SequentialCollarsCertificateLaw

/-!
# Integral and pointwise bounds for the fractional clock entrance

* `ce_lintegral_le_split` — exceptional sets paid by a second moment (AM–GM with weight `l`):
  `∫ f ≤ ∫ 1_D g + (l/2) μ(Dᶜ) + (2l)⁻¹ ∫ Φ` when `f ≤ g` on `D` and `f ≤ F`, `F² ≤ Φ` off it;
  no measurability of `f` or `D` is needed (lower integrals; `toMeasurable`).
* `ce_lintegral_indicator_le_cs` — Cauchy–Schwarz in AM–GM form:
  `∫ 1_D H ≤ (l/2) ∫ 1_D H²/G + (2l)⁻¹ ∫ G` (`G = γ^p`, `H = 0` where `G = 0`).
* `ce_measure_lt_le` (Markov), `ce_lintegral_pow_of_eLpNorm` (moments and a.e. measurability
  from an `eLpNorm` bound).
* clock facts: `ce_nearClock_posSemidef`, `ce_fracClock_nonneg`, `ce_fracClock_le`
  (`H_p ≤ W γ^p`, from `H_p ≤ W^{1-p}γ^p`), `ce_fracClock_eq_zero`;
  measurability `ce_measurable_clockTrace`, `ce_measurable_conductance`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Matrix
open scoped ENNReal ComplexOrder
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Endpoints

/-!
## Scalar inequalities
-/

/-- AM–GM: `F ≤ l/2 + F²/(2l)` for `l > 0`. -/
theorem ce_le_half_add_sq_div {F l : ℝ} (hl : 0 < l) : F ≤ l / 2 + F ^ 2 / (2 * l) := by
  have key : l / 2 + F ^ 2 / (2 * l) - F = (F - l) ^ 2 / (2 * l) := by
    field_simp; ring
  have : 0 ≤ (F - l) ^ 2 / (2 * l) := by positivity
  linarith

/-- AM–GM against a positive denominator: `H ≤ (l/2) H²/G + G/(2l)` for `G > 0`, `l > 0`. -/
theorem ce_le_cs_pointwise {H G l : ℝ} (hG : 0 < G) (hl : 0 < l) :
    H ≤ l / 2 * (H ^ 2 / G) + 1 / (2 * l) * G := by
  have h : 0 ≤ (l * H - G) ^ 2 := sq_nonneg _
  have e : l / 2 * (H ^ 2 / G) + 1 / (2 * l) * G = ((l * H) ^ 2 + G ^ 2) / (2 * l * G) := by
    field_simp
  rw [e, le_div_iff₀ (by positivity)]
  nlinarith

/-!
## Integral inequalities
-/

section Integrals

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

/-- **Exceptional sets paid by a second moment.** If `f ≤ g` on `D` and `f ≤ F` off `D` with
`F² ≤ Φ`, then `∫ f ≤ ∫ 1_D g + (l/2) μ(Dᶜ) + (2l)⁻¹ ∫ Φ` (`l > 0`; `Φ` a.e. measurable). -/
theorem ce_lintegral_le_split (D : Set Ω) (f g Φ : Ω → ℝ≥0∞) (F : Ω → ℝ)
    (hΦ : AEMeasurable Φ μ) {l : ℝ} (hl : 0 < l) (hD : ∀ ω ∈ D, f ω ≤ g ω)
    (hDc : ∀ ω ∉ D, f ω ≤ ENNReal.ofReal (F ω)) (hF : ∀ ω, ENNReal.ofReal (F ω ^ 2) ≤ Φ ω) :
    ∫⁻ ω, f ω ∂μ ≤ ∫⁻ ω, D.indicator g ω ∂μ +
      (ENNReal.ofReal (l / 2) * μ Dᶜ + ENNReal.ofReal (1 / (2 * l)) * ∫⁻ ω, Φ ω ∂μ) := by
  set B := toMeasurable μ Dᶜ
  have hB : MeasurableSet B := measurableSet_toMeasurable _ _
  have hpt : ∀ ω, f ω ≤ D.indicator g ω + (ENNReal.ofReal (l / 2) * B.indicator 1 ω +
      ENNReal.ofReal (1 / (2 * l)) * Φ ω) := by
    intro ω
    by_cases hω : ω ∈ D
    · rw [Set.indicator_of_mem hω]
      exact (hD ω hω).trans le_self_add
    · rw [Set.indicator_of_notMem hω, zero_add,
        Set.indicator_of_mem (subset_toMeasurable μ Dᶜ hω), Pi.one_apply, mul_one]
      refine (hDc ω hω).trans ?_
      have hF' : ENNReal.ofReal (l / 2) + ENNReal.ofReal (1 / (2 * l)) * ENNReal.ofReal (F ω ^ 2) ≤
          ENNReal.ofReal (l / 2) + ENNReal.ofReal (1 / (2 * l)) * Φ ω := by
        gcongr; exact hF ω
      refine le_trans ?_ hF'
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
        (by positivity)]
      exact ENNReal.ofReal_le_ofReal (by
        have := ce_le_half_add_sq_div (F := F ω) hl
        calc F ω ≤ l / 2 + F ω ^ 2 / (2 * l) := this
          _ = l / 2 + 1 / (2 * l) * F ω ^ 2 := by ring)
  have hm1 : Measurable (fun ω => ENNReal.ofReal (l / 2) * B.indicator (1 : Ω → ℝ≥0∞) ω) :=
    (measurable_one.indicator hB).const_mul _
  have hm : AEMeasurable (fun ω => ENNReal.ofReal (l / 2) * B.indicator 1 ω +
      ENNReal.ofReal (1 / (2 * l)) * Φ ω) μ :=
    hm1.aemeasurable.add (hΦ.const_mul _)
  calc ∫⁻ ω, f ω ∂μ ≤ ∫⁻ ω, (D.indicator g ω + (ENNReal.ofReal (l / 2) * B.indicator 1 ω +
        ENNReal.ofReal (1 / (2 * l)) * Φ ω)) ∂μ := lintegral_mono hpt
    _ = ∫⁻ ω, D.indicator g ω ∂μ + ∫⁻ ω, (ENNReal.ofReal (l / 2) * B.indicator 1 ω +
        ENNReal.ofReal (1 / (2 * l)) * Φ ω) ∂μ := lintegral_add_right' _ hm
    _ = _ := by
        rw [lintegral_add_left hm1,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator_one hB,
          measure_toMeasurable, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- **Cauchy–Schwarz in AM–GM form**: for `H ≥ 0`, `G ≥ 0` with `H = 0` where
`G = 0`, and `l > 0`: `∫ 1_D H ≤ (l/2) ∫ 1_D H²/G + (2l)⁻¹ ∫ G` (`G` a.e. measurable). -/
theorem ce_lintegral_indicator_le_cs (D : Set Ω) (H G : Ω → ℝ)
    (hG : AEMeasurable (fun ω => ENNReal.ofReal (G ω)) μ) (hG0 : ∀ ω, 0 ≤ G ω)
    (hHG : ∀ ω, G ω = 0 → H ω = 0) {l : ℝ} (hl : 0 < l) :
    ∫⁻ ω, D.indicator (fun ω => ENNReal.ofReal (H ω)) ω ∂μ ≤
      ENNReal.ofReal (l / 2) * ∫⁻ ω, D.indicator (fun ω => ENNReal.ofReal (H ω ^ 2 / G ω)) ω ∂μ +
        ENNReal.ofReal (1 / (2 * l)) * ∫⁻ ω, ENNReal.ofReal (G ω) ∂μ := by
  have hpt : ∀ ω, D.indicator (fun ω => ENNReal.ofReal (H ω)) ω ≤
      ENNReal.ofReal (l / 2) * D.indicator (fun ω => ENNReal.ofReal (H ω ^ 2 / G ω)) ω +
        ENNReal.ofReal (1 / (2 * l)) * ENNReal.ofReal (G ω) := by
    intro ω
    by_cases hω : ω ∈ D
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
      rcases (hG0 ω).eq_or_lt with h0 | hpos
      · rw [hHG ω h0.symm, ENNReal.ofReal_zero]; exact bot_le
      · rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        exact ENNReal.ofReal_le_ofReal (ce_le_cs_pointwise hpos hl)
    · rw [Set.indicator_of_notMem hω]; exact bot_le
  calc _ ≤ ∫⁻ ω, (ENNReal.ofReal (l / 2) *
        D.indicator (fun ω => ENNReal.ofReal (H ω ^ 2 / G ω)) ω +
        ENNReal.ofReal (1 / (2 * l)) * ENNReal.ofReal (G ω)) ∂μ := lintegral_mono hpt
    _ = _ := by
        rw [lintegral_add_right' _ (hG.const_mul _),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- **Markov** with a moment of order `m > 0`: `μ{a < f} ≤ B/a^m` when `∫ |f|^m ≤ B`. -/
theorem ce_measure_lt_le (f : Ω → ℝ) (hf : AEMeasurable f μ) {a m B : ℝ} (ha : 0 < a)
    (hm : 0 < m) (h : ∫⁻ ω, ENNReal.ofReal (|f ω| ^ m) ∂μ ≤ ENNReal.ofReal B) :
    μ {ω | a < f ω} ≤ ENNReal.ofReal (B / a ^ m) := by
  have ham : 0 < a ^ m := Real.rpow_pos_of_pos ha m
  have hsub : {ω | a < f ω} ⊆ {ω | ENNReal.ofReal (a ^ m) ≤ ENNReal.ofReal (|f ω| ^ m)} := by
    intro ω hω
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow ha.le
      ((le_of_lt hω).trans (le_abs_self _)) hm.le)
  have hmeas : AEMeasurable (fun ω => ENNReal.ofReal (|f ω| ^ m)) μ :=
    ((hf.abs).pow_const m).ennreal_ofReal
  calc μ {ω | a < f ω} ≤ μ {ω | ENNReal.ofReal (a ^ m) ≤ ENNReal.ofReal (|f ω| ^ m)} :=
        measure_mono hsub
    _ ≤ (∫⁻ ω, ENNReal.ofReal (|f ω| ^ m) ∂μ) / ENNReal.ofReal (a ^ m) :=
        meas_ge_le_lintegral_div hmeas (by simpa using ham) ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal B / ENNReal.ofReal (a ^ m) := by gcongr
    _ = ENNReal.ofReal (B / a ^ m) := (ENNReal.ofReal_div_of_pos ham).symm

/-- Moments and a.e. measurability from an `eLpNorm` bound: for `f ≥ 0`, `m ≥ 1`,
`‖f‖_m ≤ a` gives `f` a.e. strongly measurable and `∫ f^m ≤ (max a 0)^m`. -/
theorem ce_lintegral_pow_of_eLpNorm (f : Ω → ℝ) (hf0 : ∀ ω, 0 ≤ f ω) {m a : ℝ} (hm : 1 ≤ m)
    (h : eLpNorm f (ENNReal.ofReal m) μ ≤ ENNReal.ofReal a) :
    AEStronglyMeasurable f μ ∧
      ∫⁻ ω, ENNReal.ofReal (f ω ^ m) ∂μ ≤ ENNReal.ofReal (max a 0 ^ m) := by
  have hm0 : 0 < m := by linarith
  have hfin : eLpNorm f (ENNReal.ofReal m) μ ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  have hmeas := aestronglyMeasurable_of_eLpNorm_ne_top hfin
  refine ⟨hmeas, ?_⟩
  have hne0 : ENNReal.ofReal m ≠ 0 := by simpa using hm0
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hne0 ENNReal.ofReal_ne_top hmeas,
    ENNReal.toReal_ofReal hm0.le] at h
  have hint : ∫⁻ ω, ENNReal.ofReal (f ω ^ m) ∂μ = ∫⁻ ω, ‖f ω‖ₑ ^ m ∂μ := by
    refine lintegral_congr fun ω => ?_
    rw [Real.enorm_eq_ofReal (hf0 ω), ENNReal.ofReal_rpow_of_nonneg (hf0 ω) hm0.le]
  rw [hint]
  have h' : (∫⁻ ω, ‖f ω‖ₑ ^ m ∂μ) ^ (1 / m) ≤ ENNReal.ofReal (max a 0) :=
    h.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have h2 := ENNReal.rpow_le_rpow h' hm0.le
  rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hm0.ne', ENNReal.rpow_one,
    ENNReal.ofReal_rpow_of_nonneg (le_max_right _ _) hm0.le] at h2
  exact h2

end Integrals

/-!
## Clock facts
-/

theorem ce_nearClock_posSemidef (b E : ℝ) (W j : ℕ) {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x)
    (ω : GrowthPath W) : (nearClock b E W j q ω).PosSemidef := by
  have h := (intervalSource_posSemidef b E W j q hq ω).submatrix (fun x : Fin W => ((0 : Fin 2), x))
  have he : nearClock b E W j q ω =
      (intervalSource b E W j q ω).submatrix (fun x : Fin W => ((0 : Fin 2), x))
        (fun x : Fin W => ((0 : Fin 2), x)) := by
    ext x y; rfl
  rw [he]; exact h

theorem ce_clockTrace_nonneg (b E : ℝ) (W j : ℕ) {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x)
    (ω : GrowthPath W) : 0 ≤ ce_clockTrace b E W j q ω :=
  (trace_nearClock_le b E W j q hq ω).1

theorem ce_fracClock_nonneg (b E p : ℝ) (W j : ℕ) (q : ℝ → ℝ) (ω : GrowthPath W) :
    0 ≤ ce_fracClock b E p W j q ω :=
  fracTrace_nonneg p _

/-- `H_p ≤ W^{1-p} γ^p ≤ W γ^p` for `W ≥ 1`, `0 < p < 1`. -/
theorem ce_fracClock_le (b E p : ℝ) (hp : 0 < p) (hp1 : p < 1) {W : ℕ} (hW : 1 ≤ (W : ℝ))
    (j : ℕ) {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) (ω : GrowthPath W) :
    ce_fracClock b E p W j q ω ≤ (W : ℝ) * ce_clockTrace b E W j q ω ^ p := by
  have h := fracTrace_le_card_rpow_mul_trace_rpow (ce_nearClock_posSemidef b E W j hq ω) hp
    hp1.le
  rw [Fintype.card_fin] at h
  have hW1 : (W : ℝ) ^ (1 - p) ≤ (W : ℝ) := by
    calc (W : ℝ) ^ (1 - p) ≤ (W : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hW (by linarith)
      _ = W := Real.rpow_one _
  have hγ : 0 ≤ ce_clockTrace b E W j q ω ^ p :=
    Real.rpow_nonneg (ce_clockTrace_nonneg b E W j hq ω) _
  exact h.trans (mul_le_mul_of_nonneg_right hW1 hγ)

/-- The quotient convention of the paper: `γ^p = 0` forces `H_p = 0`. -/
theorem ce_fracClock_eq_zero (b E p : ℝ) (hp : 0 < p) (hp1 : p < 1) {W : ℕ} (hW : 1 ≤ (W : ℝ))
    (j : ℕ) {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) (ω : GrowthPath W)
    (h0 : ce_clockTrace b E W j q ω ^ p = 0) : ce_fracClock b E p W j q ω = 0 := by
  have := ce_fracClock_le b E p hp hp1 hW j hq ω
  rw [h0, mul_zero] at this
  exact le_antisymm this (ce_fracClock_nonneg b E p W j q ω)

theorem ce_measurable_clockTrace (b E : ℝ) (W j : ℕ) (q : ℝ → ℝ) :
    Measurable (fun ω : GrowthPath W => ce_clockTrace b E W j q ω) := by
  have hQ : Measurable (fun ω : GrowthPath W => intervalSource b E W j q ω) := by
    unfold intervalSource
    refine Measurable.of_eval_matrix _ fun x y => ?_
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    exact Finset.measurable_sum _ fun k _ =>
      measurable_const.mul (tco_measurable_tagResponse b E W j k).eval_matrix
  unfold ce_clockTrace nearClock
  refine Complex.measurable_re.comp ?_
  simp only [Matrix.trace, Matrix.diag]
  exact Finset.measurable_sum _ fun i _ =>
    ((measurable_portBlock 0 0).comp hQ).eval_matrix

theorem ce_measurable_conductance (b E : ℝ) (W j : ℕ) :
    Measurable (fun ω : GrowthPath W => pathConductance b E W j ω) := by
  have h : (fun ω : GrowthPath W => pathConductance b E W j ω) =
      fun ω => nearConductance b E (BlockBand.Internal.Contracts.Layers.pathSchur E (pathAt W j ω)) :=
    funext fun ω => pathConductance_eq b E W j ω
  rw [h]
  exact (measurable_nearConductance b E).comp ((measurable_pathSchur E).comp (measurable_pathAt W j))

end BlockBand.Endpoints
