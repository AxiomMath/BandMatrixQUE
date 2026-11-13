module

public import Mathlib

/-!
# The `L^p` assembly of the smoothing argument

The final `L^p` bookkeeping of the sharper fresh count: the sharp centered count has norm at
most `C(Wη + η^{-1/2})`. Pure measure theory on any probability space; no Gaussian law, no
spectral object.

`centered_le_of_smoothing`: let `N, X, Y, G` be real functions with `|N - X| ≤ Y`, `Y ≥ 0`,
`0 ≤ G ≤ s √Y`, `‖Y‖_1 ≤ B₁`, `‖Y‖_p ≤ B_p`, and `‖X - EX‖_p ≤ C_X ‖G‖_p`. Then
`‖N - EN‖_p ≤ B_p + B₁ + C_X s √B_p`, for every real `p ≥ 1`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Window.Count

open MeasureTheory
open scoped ENNReal

/-- **Smoothing assembly.** Law: any probability measure `μ`. Exponent: every real `p ≥ 1`.
All bounds are deterministic constants; the conclusion is uniform in everything else. -/
theorem centered_le_of_smoothing {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {p : ℝ} (hp : 1 ≤ p) (N X Y G : Ω → ℝ)
    (hNm : AEStronglyMeasurable N μ) (hXm : AEStronglyMeasurable X μ)
    (hYm : AEStronglyMeasurable Y μ) (hGm : AEStronglyMeasurable G μ)
    (hNint : Integrable N μ) (hXint : Integrable X μ)
    (hNX : ∀ ω, |N ω - X ω| ≤ Y ω) (hY0 : ∀ ω, 0 ≤ Y ω)
    (hG0 : ∀ ω, 0 ≤ G ω) (s : ℝ) (hs : 0 ≤ s) (hG : ∀ ω, G ω ≤ s * Real.sqrt (Y ω))
    (B₁ Bp Cx : ℝ) (hB₁ : 0 ≤ B₁) (hBp : 0 ≤ Bp) (hCx : 0 ≤ Cx)
    (hY1 : eLpNorm Y 1 μ ≤ ENNReal.ofReal B₁)
    (hYp : eLpNorm Y (ENNReal.ofReal p) μ ≤ ENNReal.ofReal Bp)
    (hX : eLpNorm (fun ω => X ω - ∫ ω', X ω' ∂μ) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal Cx * eLpNorm G (ENNReal.ofReal p) μ) :
    eLpNorm (fun ω => N ω - ∫ ω', N ω' ∂μ) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (Bp + B₁ + Cx * (s * Real.sqrt Bp)) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have hdecomp : (fun ω => N ω - ∫ ω', N ω' ∂μ) = fun ω =>
      ((N ω - X ω) + (X ω - ∫ ω', X ω' ∂μ)) + ((∫ ω', X ω' ∂μ) - ∫ ω', N ω' ∂μ) := by
    funext ω; ring
  rw [hdecomp]
  -- (a) the smoothing error
  have ha : eLpNorm (fun ω => N ω - X ω) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal Bp :=
    (eLpNorm_mono_real (hNm.sub hXm) fun ω => by rw [Real.norm_eq_abs]; exact hNX ω).trans hYp
  -- (b) the Gaussian gradient term
  have hsqrt : eLpNorm (fun ω => Real.sqrt (Y ω)) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (Real.sqrt Bp) := by
    have heq : (fun ω => Real.sqrt (Y ω)) = fun ω => ‖Y ω‖ ^ (1 / 2 : ℝ) := by
      funext ω; rw [Real.norm_eq_abs, abs_of_nonneg (hY0 ω), Real.sqrt_eq_rpow]
    rw [heq, eLpNorm_norm_rpow Y hYm (by norm_num)]
    have hexp : ENNReal.ofReal p * ENNReal.ofReal (1 / 2) ≤ ENNReal.ofReal p := by
      apply mul_le_of_le_one_right (by simp)
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by norm_num)
    calc eLpNorm Y (ENNReal.ofReal p * ENNReal.ofReal (1 / 2)) μ ^ (1 / 2 : ℝ)
        ≤ eLpNorm Y (ENNReal.ofReal p) μ ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow (eLpNorm_le_eLpNorm_of_exponent_le hexp) (by norm_num)
      _ ≤ ENNReal.ofReal Bp ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hYp (by norm_num)
      _ = ENNReal.ofReal (Real.sqrt Bp) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hBp (by norm_num), Real.sqrt_eq_rpow]
  have hGb : eLpNorm G (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (s * Real.sqrt Bp) := by
    calc eLpNorm G (ENNReal.ofReal p) μ
        ≤ eLpNorm (s • fun ω => Real.sqrt (Y ω)) (ENNReal.ofReal p) μ := by
          refine eLpNorm_mono_real hGm fun ω => ?_
          rw [Real.norm_eq_abs, abs_of_nonneg (hG0 ω)]
          simpa only [Pi.smul_apply, smul_eq_mul] using hG ω
      _ = ENNReal.ofReal s * eLpNorm (fun ω => Real.sqrt (Y ω)) (ENNReal.ofReal p) μ := by
          rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hs]
      _ ≤ ENNReal.ofReal s * ENNReal.ofReal (Real.sqrt Bp) := by gcongr
      _ = ENNReal.ofReal (s * Real.sqrt Bp) := (ENNReal.ofReal_mul hs).symm
  have hb : eLpNorm (fun ω => X ω - ∫ ω', X ω' ∂μ) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (Cx * (s * Real.sqrt Bp)) := by
    calc _ ≤ ENNReal.ofReal Cx * eLpNorm G (ENNReal.ofReal p) μ := hX
      _ ≤ ENNReal.ofReal Cx * ENNReal.ofReal (s * Real.sqrt Bp) := by gcongr
      _ = _ := (ENNReal.ofReal_mul hCx).symm
  -- (c) the mean difference
  have hYint : Integrable Y μ := by
    rw [← memLp_one_iff_integrable]
    exact lt_of_le_of_lt hY1 ENNReal.ofReal_lt_top
  have hYmean : (∫ ω, Y ω ∂μ) ≤ B₁ := by
    have h1 : ENNReal.ofReal (∫ ω, Y ω ∂μ) = eLpNorm Y 1 μ := by
      rw [ofReal_integral_eq_lintegral_ofReal hYint (Filter.Eventually.of_forall hY0),
        eLpNorm_one_eq_lintegral_enorm hYm]
      refine lintegral_congr fun ω => ?_
      rw [Real.enorm_eq_ofReal (hY0 ω)]
    have h2 := h1 ▸ hY1
    exact (ENNReal.ofReal_le_ofReal_iff hB₁).mp h2
  have hc : eLpNorm (fun _ : Ω => (∫ ω', X ω' ∂μ) - ∫ ω', N ω' ∂μ) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal B₁ := by
    rw [eLpNorm_const _ (by positivity) (IsProbabilityMeasure.ne_zero μ), measure_univ,
      ENNReal.one_rpow, mul_one, Real.enorm_eq_ofReal_abs]
    apply ENNReal.ofReal_le_ofReal
    rw [← integral_sub hXint hNint]
    calc |∫ ω, (X ω - N ω) ∂μ| ≤ ∫ ω, |X ω - N ω| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ ω, Y ω ∂μ := integral_mono (hXint.sub hNint).abs hYint
          (fun ω => by rw [abs_sub_comm]; exact hNX ω)
      _ ≤ B₁ := hYmean
  -- assemble
  have hm1 : AEStronglyMeasurable (fun ω => N ω - X ω) μ := hNm.sub hXm
  have hm2 : AEStronglyMeasurable (fun ω => X ω - ∫ ω', X ω' ∂μ) μ :=
    hXm.sub aestronglyMeasurable_const
  calc _ ≤ eLpNorm (fun ω => (N ω - X ω) + (X ω - ∫ ω', X ω' ∂μ)) (ENNReal.ofReal p) μ +
        eLpNorm (fun _ : Ω => (∫ ω', X ω' ∂μ) - ∫ ω', N ω' ∂μ) (ENNReal.ofReal p) μ :=
        eLpNorm_add_le hp1
    _ ≤ (eLpNorm (fun ω => N ω - X ω) (ENNReal.ofReal p) μ +
          eLpNorm (fun ω => X ω - ∫ ω', X ω' ∂μ) (ENNReal.ofReal p) μ) +
        eLpNorm (fun _ : Ω => (∫ ω', X ω' ∂μ) - ∫ ω', N ω' ∂μ) (ENNReal.ofReal p) μ := by
        gcongr
        exact eLpNorm_add_le hp1
    _ ≤ (ENNReal.ofReal Bp + ENNReal.ofReal (Cx * (s * Real.sqrt Bp))) + ENNReal.ofReal B₁ := by
        gcongr
    _ = ENNReal.ofReal (Bp + B₁ + Cx * (s * Real.sqrt Bp)) := by
        have h3 : 0 ≤ Cx * (s * Real.sqrt Bp) := by positivity
        rw [← ENNReal.ofReal_add hBp h3, ← ENNReal.ofReal_add (by positivity) hB₁]
        congr 1; ring

end BlockBand.Window.Count
