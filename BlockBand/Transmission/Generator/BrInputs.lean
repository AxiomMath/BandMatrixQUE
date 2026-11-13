module

public import BlockBand.Transmission.Generator.BrMean

/-!
# Analytic inputs of the one-layer bracket (fresh layer, bulk-uniform)

* `freshU_isHermitian`; `freshU_hp4` (`Z'_{ij}Z'_{mn}` integrable from `‖U‖² ∈ L¹`);
* **`hs_moment4_bulk`**: `E‖B‖⁴_HS ≤ (C Tr T/√W)⁴` (`oneStepFluctuation_bulk` at `p = 4`);
* `norm_ubar_sub_one_le`: `‖EU - 1‖ ≤ ‖EU - c‖ + D₀g/(2W)` (`c = meanC`, `meanC_eq`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Matrix Finset
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Transmission BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.SourceMixing BlockBand.Internal.Contracts.Layers
open BlockBand.Transmission.LengthUniform
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator ENNReal

variable {W : ℕ} {T : Matrix (Fin W) (Fin W) ℂ}

theorem freshU_isHermitian (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) : (freshU b E X ω).IsHermitian :=
  Matrix.isHermitian_mul_conjTranspose_self _

/-- Products of two centred eigenbasis entries are integrable. -/
theorem freshU_hp4 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hT : T.PosSemidef) (U : Ω → Matrix (Fin W) (Fin W) ℂ) (hUm : Measurable U)
    (h2 : Integrable (fun ω => ‖U ω‖ ^ 2) μ) (i j m n : Fin W) :
    Integrable (fun ω => ts_ent hT (U ω - matrixExpect μ U) i j *
      ts_ent hT (U ω - matrixExpect μ U) m n) μ := by
  have hZ : Measurable fun ω => U ω - matrixExpect μ U := hUm.sub_const _
  refine Integrable.mono' ((h2.const_mul 2).add (integrable_const (2 * ‖matrixExpect μ U‖ ^ 2)))
    ((ts_measurable_ent hT hZ i j).mul (ts_measurable_ent hT hZ m n)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  show ‖_ * _‖ ≤ 2 * ‖U ω‖ ^ 2 + 2 * ‖matrixExpect μ U‖ ^ 2
  rw [norm_mul]
  have a1 := ts_norm_ent_le hT (U ω - matrixExpect μ U) i j
  have a2 := ts_norm_ent_le hT (U ω - matrixExpect μ U) m n
  have a3 := norm_sub_le (U ω) (matrixExpect μ U)
  have := mul_le_mul a1 a2 (norm_nonneg _) (norm_nonneg _)
  have := mul_le_mul a3 a3 (norm_nonneg _) (by positivity)
  nlinarith [norm_nonneg (U ω), norm_nonneg (matrixExpect μ U),
    sq_nonneg (‖U ω‖ - ‖matrixExpect μ U‖)]

/-- **Fourth HS moment of `B = sand T U⁰`**, bulk-uniform. -/
theorem hs_moment4_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      ∀ hT : (passiveTransmission b E X).PosSemidef,
        Integrable (fun ω => frobSq (sand hT (freshU b E X ω -
          matrixExpect (freshLaw W b) (freshU b E X))) ^ 2) (freshLaw W b) ∧
        ∫ ω, frobSq (sand hT (freshU b E X ω - matrixExpect (freshLaw W b) (freshU b E X))) ^ 2
          ∂freshLaw W b ≤ (C / Real.sqrt W * (passiveTransmission b E X).trace.re) ^ 4 := by
  obtain ⟨C4, W4, hC4⟩ := oneStepFluctuation_bulk hA hb0 hb hκ ((4 : ℕ) : ℝ) (by norm_num)
  obtain ⟨Wi, hUi⟩ := ml_integrable_U_bulk hA hb0 hb hκ
  set C := max C4 0
  refine ⟨C, max (max W4 Wi) 1, le_max_right _ _, fun W hW E hE X hX hT => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW4, hWi⟩, hW1⟩ := hW
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  set μ := freshLaw W b
  set U := freshU b E X
  set Z : LayerSample W .oneBlockOnePort → Matrix (Fin W) (Fin W) ℂ :=
    fun ω => U ω - matrixExpect μ U
  have hZm : Measurable Z := (measurable_freshU b E X).sub_const _
  set B := fun ω => sand hT (Z ω)
  have hBm : Measurable B := (continuous_sand hT).measurable.comp hZm
  have hTr : 0 ≤ (passiveTransmission b E X).trace.re := (mm_trace_posSemidef hT).1
  have hσ : 0 ≤ C / Real.sqrt W * (passiveTransmission b E X).trace.re := by positivity
  have hS := ae_norm_sand_freshU_le hb0 hb hW1 h1 h2 hX hT
  have hSb := norm_sand_matrixExpect_le hT U (measurable_freshU b E X) (hUi W hWi E hE X hX) hS
  have hB2 : ∀ᵐ ω ∂μ, ‖B ω‖ ≤ 2 := by
    filter_upwards [hS] with ω hω
    have : B ω = sand hT (U ω) - sand hT (matrixExpect μ U) := sand_sub hT _ _
    rw [this]; exact (norm_sub_le _ _).trans (by linarith)
  have hfr : ∀ᵐ ω ∂μ, frobSq (B ω) ≤ 4 * W := by
    filter_upwards [hB2] with ω hω
    refine (frobSq_le_card _).trans ?_
    have := pow_le_pow_left₀ (norm_nonneg _) hω 2
    nlinarith [Nat.cast_nonneg (α := ℝ) W]
  have hhs : ∀ ω, hsSandwich (passiveTransmission b E X) (Z ω) = Real.sqrt (frobSq (B ω)) :=
    fun ω => by
      rw [frobSq_sand, Real.sqrt_sq (show 0 ≤ hsSandwich (passiveTransmission b E X) (Z ω) from
        Real.sqrt_nonneg _)]
  have hb' : ∀ u v : Fin W → ℂ, eLpNorm (fun ω => bilinear u (Z ω) v)
      (ENNReal.ofReal ((4 : ℕ) : ℝ)) μ ≤ ENNReal.ofReal (C / Real.sqrt W * vecNorm u * vecNorm v) :=
    fun u v => ((hC4 W hW4 E hE X hX u v).1).trans (ENNReal.ofReal_le_ofReal (by
      have := vecNorm_nonneg u; have := vecNorm_nonneg v
      have : C4 / Real.sqrt W ≤ C / Real.sqrt W :=
        div_le_div_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
      gcongr))
  have h := eLpNorm_hsSandwich_le μ hT hZm (p := ENNReal.ofReal ((4 : ℕ) : ℝ))
    (by rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num]
        exact ENNReal.ofReal_le_ofReal (by norm_num))
    (by positivity) hb'
  simp only [hhs] at h
  have hm4 := mp_integral_pow_le (Filter.Eventually.of_forall fun _ => Real.sqrt_nonneg _) 4
    (by norm_num) hσ h
  have hFm : Measurable fun ω => frobSq (B ω) := continuous_frobSq.measurable.comp hBm
  have hq : ∀ ω, Real.sqrt (frobSq (B ω)) ^ 4 = frobSq (B ω) ^ 2 := fun ω => by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (frobSq_nonneg _)]
  refine ⟨?_, ?_⟩
  · refine Integrable.of_bound (hFm.pow_const 2).aestronglyMeasurable ((4 * W) ^ 2) ?_
    filter_upwards [hfr] with ω hω
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (frobSq_nonneg _) hω 2
  · calc ∫ ω, frobSq (B ω) ^ 2 ∂μ = ∫ ω, Real.sqrt (frobSq (B ω)) ^ 4 ∂μ :=
          integral_congr_ae (Filter.Eventually.of_forall fun ω => (hq ω).symm)
      _ ≤ _ := hm4

/-- `‖EU - 1‖ ≤ ‖EU - c‖ + D₀g/(2W)`. -/
theorem norm_ubar_sub_one_le {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    (hD0 : 0 ≤ transportD0 b E) {X : Matrix (Fin W) (Fin W) ℂ} (hX : (passiveY X).PosSemidef)
    (Ub : Matrix (Fin W) (Fin W) ℂ) :
    ‖Ub - 1‖ ≤ ‖Ub - ((meanC b E X : ℝ) : ℂ) • 1‖ +
      transportD0 b E * (passiveTransmission b E X).trace.re / (2 * W) := by
  have hT := passiveTransmission_posSemidef (b := b) (by linarith) h1 h2 hX
  have hg : 0 ≤ (passiveTransmission b E X).trace.re := (mm_trace_posSemidef hT).1
  set y := transportD0 b E * (passiveTransmission b E X).trace.re / (2 * W)
  have hy : 0 ≤ y := by positivity
  have hc := meanC_eq hb0 hb h1 h2 X
  have hc1 : |1 - meanC b E X| ≤ y := by
    rw [hc]
    have hpos : 0 < 1 + y := by linarith
    rw [show 1 - (1 + y)⁻¹ = y / (1 + y) by field_simp; ring, abs_of_nonneg (by positivity)]
    exact div_le_self hy (by linarith)
  have e : Ub - 1 = (Ub - ((meanC b E X : ℝ) : ℂ) • 1) + ((meanC b E X - 1 : ℝ) : ℂ) • 1 := by
    rw [Complex.ofReal_sub, sub_smul, Complex.ofReal_one, one_smul]; abel
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  refine (norm_smul_le _ _).trans ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
  exact (mul_le_of_le_one_right (abs_nonneg _) PassiveLayer.norm_one_le').trans hc1

end BlockBand.Transmission.Generator
