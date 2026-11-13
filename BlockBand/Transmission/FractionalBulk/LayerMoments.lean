module

public import BlockBand.Transmission.FractionalBulk.LayerSample
public import BlockBand.Transmission.FractionalBulk.Weighted
public import BlockBand.Transmission.FractionalBulk.MeanOp
public import BlockBand.Transmission.LengthUniform.BulkMassLayer
public import BlockBand.SourceProcess.FullSource.MomentStep
public import BlockBand.Transmission.SourceMixing.Conductance

/-!
# Fourth moments of one fresh layer, uniformly on the bulk

* `pow4_of_eLpNorm`: `‖f‖_4 ≤ C` gives `f⁴` integrable and `E f⁴ ≤ C⁴`;
* `layerMoments_bulk`: `E‖L‖⁴ ≤ C_L⁴` for every passive `X`;
* `layerBil4_bulk`: `E|u*(U - EU)v|⁴ ≤ C_B⁴/W²` for unit `u, v` (`U = LL*`), the paper's
  "fourth centered moment is `O(W⁻²)`".
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.FractionalBulk

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.SourceMixing
open scoped ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- From `‖f‖_{L⁴} ≤ C` to `E f⁴ ≤ C⁴` (and integrability), `f ≥ 0`. -/
theorem pow4_of_eLpNorm {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) (hf0 : ∀ ω, 0 ≤ f ω) {C : ℝ} (hC : 0 ≤ C)
    (h : eLpNorm f (ENNReal.ofReal 4) μ ≤ ENNReal.ofReal C) :
    Integrable (fun ω => f ω ^ 4) μ ∧ ∫ ω, f ω ^ 4 ∂μ ≤ C ^ 4 := by
  have hlt : eLpNorm f (ENNReal.ofReal 4) μ < ∞ := lt_of_le_of_lt h ENNReal.ofReal_lt_top
  have hmem : MemLp f (ENNReal.ofReal 4) μ := hlt
  have hmem' : MemLp f ((4 : ℕ) : ℝ≥0∞) μ := by
    have : ENNReal.ofReal 4 = ((4 : ℕ) : ℝ≥0∞) := by norm_num
    rwa [this] at hmem
  have hint : Integrable (fun ω => f ω ^ 4) μ := by
    have := hmem'.integrable_norm_pow' (p := 4)
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Real.norm_of_nonneg (hf0 ω)]
  refine ⟨hint, ?_⟩
  have hl := SourceMixing.cm_lintegral_le hf (p := 4) (by norm_num) hC h
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω => pow_nonneg (hf0 ω) 4)
    hint.aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) (le_trans (le_of_eq ?_) (hl.trans
    (le_of_eq (by rw [show (C ^ (4 : ℝ)) = C ^ 4 by norm_cast]))))
  refine lintegral_congr fun ω => ?_
  rw [← ofReal_norm, Real.norm_of_nonneg (hf0 ω),
    ENNReal.ofReal_rpow_of_nonneg (hf0 ω) (by norm_num)]
  norm_cast

/-- **`E‖L‖⁴ ≤ C_L⁴`**, bulk-uniform. -/
theorem layerMoments_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (CL : ℝ) (W₀ : ℕ), 0 ≤ CL ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
        Integrable (fun y => ‖freshL b E X y‖ ^ 4) (freshLaw W b) ∧
        ∫ y, ‖freshL b E X y‖ ^ 4 ∂freshLaw W b ≤ CL ^ 4 := by
  obtain ⟨C4, W4, h4⟩ := hA.moments b hb0 hb _ hκ 4 (by norm_num)
  refine ⟨max C4 0, W4, le_max_right _ _, fun W hW E hE X hX => ?_⟩
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  have hz := PassiveLayer.boundaryZ_mem_paramDisk (b := b) (by linarith) h1 h2
  have m4 := (h4 W hW E hE _ hz X hX).2.2.2
  exact pow4_of_eLpNorm (measurable_norm_freshL b E X).aestronglyMeasurable
    (fun _ => norm_nonneg _) (le_max_right _ _) (m4.trans (ENNReal.ofReal_le_ofReal
      (le_max_left _ _)))

/-- **`E|u*(U - EU)v|⁴ ≤ C_B⁴/W²`** for unit vectors, bulk-uniform. -/
theorem layerBil4_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (CB : ℝ) (W₀ : ℕ), 0 ≤ CB ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef → ∀ u v : Fin W → ℂ,
        vecNorm u = 1 → vecNorm v = 1 →
        Integrable (fun y => ‖bilinear u (freshU b E X y -
          matrixExpect (freshLaw W b) (freshU b E X)) v‖ ^ 4) (freshLaw W b) ∧
        ∫ y, ‖bilinear u (freshU b E X y - matrixExpect (freshLaw W b) (freshU b E X)) v‖ ^ 4
          ∂freshLaw W b ≤ CB ^ 4 / (W : ℝ) ^ 2 := by
  obtain ⟨C, W₁, h⟩ := hA.bilinear b hb0 hb _ hκ 4 (by norm_num)
  refine ⟨max C 0, max W₁ 1, le_max_right _ _, fun W hW E hE X hX u v hu hv => ?_⟩
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast le_trans (le_max_right _ _) hW
  have hz := PassiveLayer.boundaryZ_mem_paramDisk (b := b) (by linarith) h1 h2
  have hb4 := (h W (le_trans (le_max_left _ _) hW) E hE _ hz X hX u v).1
  rw [hu, hv, mul_one, mul_one] at hb4
  have hb4' : eLpNorm (fun y => ‖bilinear u (freshU b E X y -
      matrixExpect (freshLaw W b) (freshU b E X)) v‖) (ENNReal.ofReal 4) (freshLaw W b) ≤
      ENNReal.ofReal (max C 0 / Real.sqrt W) := by
    rw [eLpNorm_norm _ (measurable_bilinear_centered b E X _ u v).aestronglyMeasurable]
    exact hb4.trans (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)))
  have hm := (measurable_bilinear_centered b E X
    (matrixExpect (freshLaw W b) (freshU b E X)) u v).norm
  obtain ⟨hi, hI⟩ := pow4_of_eLpNorm hm.aestronglyMeasurable (fun _ => norm_nonneg _)
    (by positivity) hb4'
  refine ⟨hi, hI.trans (le_of_eq ?_)⟩
  have hs : Real.sqrt W ^ 4 = (W : ℝ) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, Real.sq_sqrt (by positivity)]
  rw [div_pow, hs]

end BlockBand.Transmission.FractionalBulk
