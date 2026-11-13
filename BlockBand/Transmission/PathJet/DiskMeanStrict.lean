module

public import BlockBand.Transmission.PathJet.DiskMeanPhys

/-!
# The one-port mean equations on the parameter disk, strictly passive inputs (bundle)

`diskMeanEquationsStrict_holds (hA : PassiveBoundsStatement) : DiskMeanEquationsStrict`:
`b, κ` first; then `C_v, ι₀ > 0, C, W₀`; for `W ≥ W₀`, `E ∈ bulkInterval κ`,
`w ∈ paramDisk b E` and every strictly passive `X` (`Y ≻ 0`), the means `v = vW`, `u = uW`
satisfy `Im v ≤ 0`, `|v| ≤ C_v`, `Im ζ ≥ ι₀` and both mean equations with error `C/W²`.

The lower bound on `Im ζ = (1-2b)(-Im v) + b(-Im u)` is from the port equation: with
`D = w - bv`, `Im D ≥ Im w ≥ η_κ/2`, `|D| ≤ 3 + bC_v`, and `uD = 1 + O(W⁻²)`
(`neg_im_le_of_mul`).
The general passive case is obtained afterwards by the `regX` limit (as in `MeanStepLimit`),
since `Y ≻ 0` holds only almost surely along the path.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PathJet

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PathScalar
open BlockBand.Transmission.Bridge
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- `Im w ≥ η/2` and `|w| ≤ 3` on the parameter disk (bulk `E`, `b < 1`). -/
theorem paramDisk_bounds {b E : ℝ} (hb0 : 0 < b) (hb : b < 1) (h1 : -2 < E) (h2 : E < 2)
    {w : ℂ} (hw : w ∈ paramDisk b E) : etaZ b E / 2 ≤ w.im ∧ ‖w‖ ≤ 3 := by
  have hd : ‖w - boundaryZ b E‖ ≤ etaZ b E / 2 := by
    rw [paramDisk, Metric.mem_closedBall, dist_eq_norm] at hw; exact hw
  have hz : ‖boundaryZ b E‖ ≤ 2 := by
    rw [boundaryZ]
    refine (norm_add_le _ _).trans ?_
    rw [norm_inv, norm_mul, norm_matchedA E h1 h2, Complex.norm_real, Real.norm_of_nonneg hb0.le]
    linarith
  have hη : etaZ b E ≤ 2 := (Complex.im_le_norm _).trans hz
  have him : |w.im - (boundaryZ b E).im| ≤ etaZ b E / 2 := by
    rw [← Complex.sub_im]; exact (Complex.abs_im_le_norm _).trans hd
  refine ⟨?_, ?_⟩
  · have := (abs_le.mp him).1; rw [etaZ] at *; linarith
  · calc ‖w‖ = ‖(w - boundaryZ b E) + boundaryZ b E‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
      _ ≤ 3 := by linarith

/-- `-Im u ≥ h/(2M²)` from `|uD - 1| ≤ δ`, `Im D ≥ h`, `|D| ≤ M`, `δ ≤ h/(2(h+M))`. -/
theorem neg_im_le_of_mul {u D : ℂ} {h M δ : ℝ} (hh : 0 < h) (hD : h ≤ D.im) (hM : ‖D‖ ≤ M)
    (hr : ‖u * D - 1‖ ≤ δ) (hδ : δ ≤ h / (2 * (h + M))) : h / (2 * M ^ 2) ≤ -u.im := by
  have hDpos : 0 < D.im := lt_of_lt_of_le hh hD
  have hD0 : D ≠ 0 := fun h0 => by rw [h0] at hDpos; simp at hDpos
  have hDn : h ≤ ‖D‖ := hD.trans (Complex.im_le_norm _)
  have hMpos : 0 < M := lt_of_lt_of_le hh (hDn.trans hM)
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hr
  set t := u * D
  have hu : u = t * D⁻¹ := by simp only [t]; field_simp
  have hns : 0 < Complex.normSq D := Complex.normSq_pos.mpr hD0
  have hns' : Complex.normSq D ≤ M ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]; gcongr
  have hre : 1 - δ ≤ t.re := by
    have := (Complex.abs_re_le_norm (t - 1)).trans hr
    rw [Complex.sub_re, Complex.one_re] at this
    linarith [(abs_le.mp this).1]
  have him : |t.im| ≤ δ := by
    have := (Complex.abs_im_le_norm (t - 1)).trans hr
    simpa using this
  have hDre : |D.re| ≤ M := (Complex.abs_re_le_norm D).trans hM
  have hnum : h / 2 ≤ t.re * D.im - t.im * D.re := by
    have h1 : (1 - δ) * h ≤ t.re * D.im := by
      have : 0 ≤ 1 - δ := by
        have : h / (2 * (h + M)) ≤ 1 := by
          rw [div_le_one (by positivity)]; linarith
        linarith
      calc (1 - δ) * h ≤ (1 - δ) * D.im := by gcongr
        _ ≤ t.re * D.im := by gcongr
    have h2 : t.im * D.re ≤ δ * M := by
      calc t.im * D.re ≤ |t.im * D.re| := le_abs_self _
        _ = |t.im| * |D.re| := abs_mul _ _
        _ ≤ δ * M := by gcongr
    have h3 : δ * (h + M) ≤ h / 2 := by
      rw [le_div_iff₀ (by positivity)] at hδ; nlinarith
    nlinarith
  have hval : -u.im = (t.re * D.im - t.im * D.re) / Complex.normSq D := by
    rw [hu, Complex.mul_im, Complex.inv_re, Complex.inv_im]; field_simp; ring
  rw [hval, div_le_div_iff₀ (by positivity) hns]
  calc h * Complex.normSq D ≤ h * M ^ 2 := by gcongr
    _ = h / 2 * (2 * M ^ 2) / 1 := by ring
    _ ≤ (t.re * D.im - t.im * D.re) * (2 * M ^ 2) := by rw [div_one]; gcongr

/-- `Im ⟨𝒢₁₁(w)⟩ ≤ 0` at Hermitian samples (strictly passive `X`, `Im w > 0`). -/
theorem im_physTrW_nonpos (E : ℝ) {w : ℂ} (hw : 0 < w.im) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosDef) (ω : LayerSample W .oneBlockOnePort) (hA : (ω.1 0).IsHermitian) :
    (physTrW E w X ω).im ≤ 0 := by
  have hpd : (matrixImaginaryPart (layerMatrix .oneBlockOnePort E w
      (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) ω)).PosDef := by
    rw [im_layerMatrix_eq E w X ω hA]
    exact posDef_fromBlocks_diag (posDef_liftX hY) (Matrix.PosDef.one.smul hw)
  have h := neg_im_inv_posSemidef _ hpd.posSemidef
  have hd : ∀ x, (gW E w X ω (phys x) (phys x)).im ≤ 0 := fun x => by
    have h1 := h.diag_nonneg (i := phys x)
    rw [diag_negIm] at h1
    have := (Complex.nonneg_iff.mp h1).1
    simp at this; exact this
  have e : (physTrW E w X ω).im = (W : ℝ)⁻¹ * ∑ x, (gW E w X ω (phys x) (phys x)).im := by
    simp [physTrW, trace_letter0_w, Complex.im_sum]
  rw [e]
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (Finset.sum_nonpos fun x _ => hd x)

theorem norm_physTrW_le (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) : ‖physTrW E w X ω‖ ≤ ‖gW E w X ω‖ := by
  rcases Nat.eq_zero_or_pos W with rfl | hW
  · simp [physTrW]
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  rw [physTrW, trace_letter0_w, norm_mul, norm_inv, Complex.norm_natCast]
  calc (W : ℝ)⁻¹ * ‖∑ y, gW E w X ω (phys y) (phys y)‖
      ≤ (W : ℝ)⁻¹ * ∑ _y : Fin W, ‖gW E w X ω‖ := by
        gcongr; exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => norm_entry_le' _ _ _)
    _ = ‖gW E w X ω‖ := by simp; field_simp

/-- **The mean equations on the parameter disk, strictly passive inputs.** -/
def DiskMeanEquationsStrict : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (Cv ι₀ C : ℝ) (W₀ : ℕ), 0 ≤ Cv ∧ 0 < ι₀ ∧ 0 ≤ C ∧
      ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ w ∈ paramDisk b E,
        ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosDef →
          (vW b E w X).im ≤ 0 ∧ ‖vW b E w X‖ ≤ Cv ∧
          ι₀ ≤ (zetaOf b E (vW b E w X) (uW b E w X)).im ∧
          ‖uW b E w X * (w - (b : ℂ) * vW b E w X) - 1‖ ≤ C / (W : ℝ) ^ 2 ∧
          ‖vW b E w X - stieltjes X (zetaOf b E (vW b E w X) (uW b E w X))‖ ≤ C / (W : ℝ) ^ 2

theorem diskMeanEquationsStrict_holds (hA : PassiveBoundsStatement) : DiskMeanEquationsStrict := by
  intro b hb0 hb κ hκ
  obtain ⟨C1, W1, m1⟩ := layer_moments_w hA hb0 hb hκ 1 le_rfl
  set Cv := max C1 0
  have hCv : 0 ≤ Cv := le_max_right _ _
  set h := etaLow b κ / 2
  have hh : 0 < h := by have := etaLow_pos (by linarith : b < 1) hκ; positivity
  set M := 3 + b * Cv
  have hM : 0 < M := by positivity
  set ι₀ := b * (h / (2 * M ^ 2))
  have hι : 0 < ι₀ := by positivity
  set δ := h / (2 * (h + M))
  have hδ : 0 < δ := by positivity
  obtain ⟨Cp, Wp, hCp, hport⟩ := meanEq_port_w hA hb0 hb hκ
  obtain ⟨Cf, Wf, hCf, hphys⟩ := meanEq_phys_w hA hb0 hb hκ hι
  refine ⟨Cv, ι₀, max Cp Cf, max (max W1 Wp) (max Wf (⌈Cp / δ⌉₊ + 1)), hCv, hι,
    le_trans hCp (le_max_left _ _), fun W hW E hE w hwD X hX => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW1, hWp⟩, hWf, hWe⟩ := hW
  obtain ⟨h1, h2⟩ := bulk_bounds hκ hE
  obtain ⟨hwim, hwn⟩ := paramDisk_bounds hb0 (by linarith) h1 h2 hwD
  have hηl := etaLow_le (by linarith : b < 1) hκ hE
  have hwh : h ≤ w.im := by simp only [h]; linarith
  have hw : 0 < w.im := lt_of_lt_of_le hh hwh
  have hx : (1 : ℝ) ≤ W := by exact_mod_cast (by omega : 1 ≤ W)
  set μ := layerLaw W b .oneBlockOnePort
  set v := vW b E w X
  set u := uW b E w X
  have hm := m1 W hW1 E hE w hwD X hX.posSemidef
  have hGm : Measurable fun ω => ‖gW E w X ω‖ :=
    continuous_norm.measurable.comp (measurable_layerRes (W := W) E w X)
  have hl : ∫⁻ ω, ‖‖gW E w X ω‖‖ₑ ∂μ ≤ ENNReal.ofReal C1 := by
    have := hm
    rwa [show ENNReal.ofReal 1 = 1 by simp,
      eLpNorm_one_eq_lintegral_enorm hGm.aestronglyMeasurable] at this
  have hGi : Integrable (fun ω => ‖gW E w X ω‖) μ :=
    ⟨hGm.aestronglyMeasurable, lt_of_le_of_lt hl ENNReal.ofReal_lt_top⟩
  have hPm : Measurable fun ω => physTrW E w X ω := by
    simp only [physTrW, trace_letter0_w]
    exact measurable_const.mul (Finset.measurable_sum _ fun y _ =>
      (measurable_layerRes (W := W) E w X).eval_matrix)
  have hPi : Integrable (fun ω => physTrW E w X ω) μ :=
    hGi.mono' hPm.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => norm_physTrW_le E w X ω)
  have hv0 : v.im ≤ 0 := by
    have : v.im = ∫ ω, (physTrW E w X ω).im ∂μ := (integral_im hPi).symm
    rw [this]
    exact integral_nonpos_of_ae ((ae_layer_herm b).mono fun ω hA => im_physTrW_nonpos E hw hX ω hA)
  have hvC : ‖v‖ ≤ Cv := by
    have hint : ∫ ω, ‖gW E w X ω‖ ∂μ ≤ Cv := by
      rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω => norm_nonneg _)
        hGm.aestronglyMeasurable]
      have hl' : ∫⁻ ω, ENNReal.ofReal ‖gW E w X ω‖ ∂μ ≤ ENNReal.ofReal C1 := by
        simpa [Real.enorm_eq_ofReal (norm_nonneg _)] using hl
      exact ENNReal.toReal_le_of_le_ofReal hCv (hl'.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
    calc ‖v‖ ≤ ∫ ω, ‖physTrW E w X ω‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ ω, ‖gW E w X ω‖ ∂μ := integral_mono hPi.norm hGi fun ω => norm_physTrW_le E w X ω
      _ ≤ Cv := hint
  have hεW : Cp / (W : ℝ) ^ 2 ≤ δ := by
    have hc := Nat.le_ceil (Cp / δ)
    have hc' : ((⌈Cp / δ⌉₊ : ℕ) : ℝ) ≤ W := by exact_mod_cast (by omega : ⌈Cp / δ⌉₊ ≤ W)
    have hWW : (W : ℝ) ≤ (W : ℝ) ^ 2 := by nlinarith
    have h1' : Cp / δ ≤ (W : ℝ) ^ 2 := by linarith
    rw [div_le_iff₀ hδ] at h1'
    rw [div_le_iff₀ (by positivity)]; linarith
  have hs := hport W hWp E hE w hwD hw X hX
  have hDim : h ≤ (w - (b : ℂ) * v).im := by
    have : (w - (b : ℂ) * v).im = w.im - b * v.im := by simp
    rw [this]; nlinarith
  have hDn : ‖w - (b : ℂ) * v‖ ≤ M := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hb0.le]
    simp only [M]; gcongr
  have hui := neg_im_le_of_mul hh hDim hDn (hs.trans hεW) le_rfl
  have hζ : ι₀ ≤ (zetaOf b E v u).im := by
    rw [im_zetaOf]
    have : 0 ≤ (1 - 2 * b) * (-v.im) := mul_nonneg (by linarith) (by linarith)
    simp only [ι₀]; nlinarith
  have hf := hphys W hWf E hE w hwD hw X hX hζ
  have hdiv : ∀ c : ℝ, c ≤ max Cp Cf → c / (W : ℝ) ^ 2 ≤ max Cp Cf / (W : ℝ) ^ 2 := fun c hc =>
    div_le_div_of_nonneg_right hc (by positivity)
  exact ⟨hv0, hvC, hζ, hs.trans (hdiv _ (le_max_left _ _)), hf.trans (hdiv _ (le_max_right _ _))⟩

end BlockBand.Transmission.PathJet
