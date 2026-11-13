module

public import BlockBand.SourceProcess.FullSource.Conversion
public import BlockBand.SourceProcess.FullSource.Statement

/-!
# The one-layer inputs of the tag recursion, uniformly on a bulk interval

`tagLayerBounds_of`: the full-source estimates and the passive mean and fluctuation steps give the
one-layer bounds `TagLayerBounds` used by the tag recursion, with constants uniform for `W ≥ W₀`
and `E` in a bulk interval.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSource

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.Transmission.PathScalar
open scoped ENNReal ComplexOrder Matrix.Norms.L2Operator

theorem bilinear_bound_mono {W : ℕ} {C C' : ℝ} (h : C ≤ C') (u v : Fin 2 × Fin W → ℂ) :
    ENNReal.ofReal (C / Real.sqrt W * vecNorm u * vecNorm v) ≤
      ENNReal.ofReal (C' / Real.sqrt W * vecNorm u * vecNorm v) := by
  refine ENNReal.ofReal_le_ofReal ?_
  have hu := BlockBand.Transmission.PassiveCovariance.vecNorm_nonneg u
  have hv := BlockBand.Transmission.PassiveCovariance.vecNorm_nonneg v
  have : C / Real.sqrt W ≤ C' / Real.sqrt W :=
    div_le_div_of_nonneg_right h (Real.sqrt_nonneg _)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hu) hv

/-- **The bundled one-layer inputs, uniformly on a bulk interval.** -/
theorem tagLayerBounds_of (hFS : FullSourceEstimates) (hMS : PassiveMeanStep)
    (hFl : PassiveFluctuationStep) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ)
    {n : ℕ} (hn : 2 ≤ n) :
    ∃ (Ca C₂ Cn CN₂ CN Cf Cm ρ d₀ : ℝ) (W₀ : ℕ), 0 ≤ Ca ∧ 0 ≤ C₂ ∧ 0 ≤ Cn ∧ 0 ≤ CN ∧
      0 ≤ Cf ∧ 0 ≤ Cm ∧ 0 ≤ ρ ∧ ρ < 1 ∧ 0 < d₀ ∧
      ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
        TagLayerBounds b E W n Ca C₂ Cn CN₂ CN Cf Cm ρ d₀ := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  obtain ⟨Ca, Wa, hCa⟩ := hFS.mean b hb0 hb κ hκ
  obtain ⟨d₁, hd₁, hfl⟩ := hFS.fluct b hb0 hb κ hκ
  obtain ⟨C₂, W₂, hC₂⟩ := hfl 2 (by norm_num)
  obtain ⟨Cn, Wn, hCn⟩ := hfl n hn1
  obtain ⟨CN₂, WN₂, hCN₂⟩ := hFS.moments b hb0 hb κ hκ 2 (by norm_num)
  obtain ⟨CN, WN, hCN⟩ := hFS.moments b hb0 hb κ hκ ((2 * (2 * n) : ℕ) : ℝ)
    (by exact_mod_cast (show 1 ≤ 2 * (2 * n) by omega))
  obtain ⟨Cf, Wf, hCf0, hCf⟩ := hFl b hb0 hb κ hκ 2 (by norm_num)
  obtain ⟨d₀, ρ, Cm, Wm, hd₀, hρ0, hρ1, hCm, hm⟩ := hMS b hb0 hb κ hκ
  refine ⟨max Ca 0, max C₂ 0, max Cn 0, CN₂, max CN 0, Cf, Cm, ρ, min d₀ d₁,
    max (max (max Wa W₂) (max Wn WN₂)) (max (max WN Wf) Wm), le_max_right _ _,
    le_max_right _ _, le_max_right _ _, le_max_right _ _, hCf0, hCm, hρ0, hρ1,
    lt_min hd₀ hd₁, ?_⟩
  intro W hW E hE
  have hWa : Wa ≤ W := le_trans (by simp) hW
  have hW₂ : W₂ ≤ W := le_trans (by simp) hW
  have hWn : Wn ≤ W := le_trans (by simp) hW
  have hWN₂ : WN₂ ≤ W := le_trans (by simp) hW
  have hWN : WN ≤ W := le_trans (by simp) hW
  have hWf : Wf ≤ W := le_trans (by simp) hW
  have hWm : Wm ≤ W := le_trans (by simp) hW
  refine ⟨fun XX hXX => ?_, fun XX hXX hd u v => ?_, fun XX hXX hd u v => ?_, fun XX hXX => ?_,
    fun XX hXX => ?_, fun X hX => ?_, fun X hX hd => ?_⟩
  · refine (hCa W hWa E hE XX hXX).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
    exact add_nonneg (norm_nonneg _) (sq_nonneg _)
  · exact (hC₂ W hW₂ E hE XX hXX (hd.trans (min_le_right _ _)) u v).trans
      (bilinear_bound_mono (le_max_left _ _) u v)
  · exact (hCn W hWn E hE XX hXX (hd.trans (min_le_right _ _)) u v).trans
      (bilinear_bound_mono (le_max_left _ _) u v)
  · have := (hCN₂ W hWN₂ E hE XX hXX).1
    rwa [show ENNReal.ofReal 2 = 2 by simp] at this
  · exact (hCN W hWN E hE XX hXX).1.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  · exact hCf W hWf E hE X hX
  · exact hm W hWm E hE X hX (hd.trans (min_le_left _ _))

end BlockBand.SourceProcess.FullSource
