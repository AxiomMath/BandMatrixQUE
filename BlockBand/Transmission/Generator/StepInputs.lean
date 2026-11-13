module

public import BlockBand.Transmission.Generator.StepMain
public import BlockBand.Transmission.LengthUniform.BulkMassLayer
public import BlockBand.Transmission.PassiveCovariance.VitaliL2
public import BlockBand.Transmission.PassiveCovariance.Regularization
public import BlockBand.Transmission.SourceMixing.MassPath

/-!
# Analytic inputs of the `k ≥ 2` one-layer drift (fresh layer, bulk-uniform)

* `norm_sand_matrixExpect_le`: `‖sand T (EU)‖ ≤ 1` from `‖sand T U‖ ≤ 1` a.s.;
* `freshU_sq_integrable_bulk`: `‖U‖²` integrable (`‖L‖ ∈ L⁴`), hence the covariance products
  (`freshU_hp`);
* `frobSq_le_card`: `‖B‖²_HS ≤ W‖B‖²`; `continuous_frobSq`;
* `hs_moments_bulk`: `E‖B‖²_HS ≤ (C Tr T/√W)²`, `E‖B‖‖B‖²_HS ≤ (C Tr T/√W)³`.
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

theorem continuous_frobSq : Continuous (frobSq : Matrix (Fin W) (Fin W) ℂ → ℝ) := by
  unfold frobSq
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    (continuous_norm.comp ((continuous_apply j).comp (continuous_apply i))).pow 2

theorem frobSq_le_card (B : Matrix (Fin W) (Fin W) ℂ) : frobSq B ≤ ‖B‖ ^ 2 * W := by
  have h := frobSq_mul_left_le B 1
  rw [Matrix.mul_one] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  rw [frobSq]
  have : ∀ i : Fin W, ∑ j, ‖(1 : Matrix (Fin W) (Fin W) ℂ) i j‖ ^ 2 = 1 := fun i => by
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [Matrix.one_apply_ne (Ne.symm hj)])
      (by simp)]
    simp
  simp [this]

theorem sand_matrixExpect {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (hT : T.PosSemidef)
    (U : Ω → Matrix (Fin W) (Fin W) ℂ) (hUi : ∀ i j, Integrable (fun ω => U ω i j) μ) :
    sand hT (matrixExpect μ U) = matrixExpect μ (fun ω => sand hT (U ω)) := by
  ext i m
  rw [show matrixExpect μ (fun ω => sand hT (U ω)) i m = ∫ ω, sand hT (U ω) i m ∂μ from rfl]
  simp only [sand_apply, ts_ent]
  rw [bilinear_matrixExpect U _ _ hUi, integral_const_mul]

theorem norm_sand_matrixExpect_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hT : T.PosSemidef) (U : Ω → Matrix (Fin W) (Fin W) ℂ)
    (hUm : Measurable U) (hUi : ∀ i j, Integrable (fun ω => U ω i j) μ)
    (hS : ∀ᵐ ω ∂μ, ‖sand hT (U ω)‖ ≤ 1) : ‖sand hT (matrixExpect μ U)‖ ≤ 1 := by
  rw [sand_matrixExpect hT U hUi]
  have hm : Measurable fun ω => sand hT (U ω) := (continuous_sand hT).measurable.comp hUm
  have hn : Integrable (fun ω => ‖sand hT (U ω)‖) μ :=
    Integrable.of_bound hm.norm.aestronglyMeasurable 1 (by
      filter_upwards [hS] with ω hω; rwa [Real.norm_of_nonneg (norm_nonneg _)])
  have hG : ∀ i j, Integrable (fun ω => sand hT (U ω) i j) μ := fun i j => by
    simp only [sand_apply, ts_ent]
    exact (integrable_bilinear U hUi _ _).const_mul _
  refine (norm_matrixExpect_le _ hG hn).trans ?_
  calc ∫ ω, ‖sand hT (U ω)‖ ∂μ ≤ ∫ _ω, (1 : ℝ) ∂μ := integral_mono_ae hn (integrable_const _) hS
    _ = 1 := by simp

/-- `‖U‖²` is integrable (`‖L‖ ∈ L⁴`), bulk-uniformly. -/
theorem freshU_sq_integrable_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosSemidef → Integrable (fun ω => ‖freshU b E X ω‖ ^ 2) (freshLaw W b) := by
  obtain ⟨C4, W4, h4⟩ := hA.moments b hb0 hb _ hκ 4 (by norm_num)
  refine ⟨W4, fun W hW E hE X hX => ?_⟩
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  have hz := PassiveLayer.boundaryZ_mem_paramDisk (b := b) (by linarith) h1 h2
  have m4 := (h4 W hW E hE _ hz X hX).2.2.2
  have hmem : MemLp (fun ω => ‖freshL b E X ω‖) ((4 : ℕ) : ℝ≥0∞) (freshLaw W b) := by
    have : ENNReal.ofReal (4 : ℝ) = ((4 : ℕ) : ℝ≥0∞) := by norm_num
    rw [MemLp, ← this]; exact m4.trans_lt ENNReal.ofReal_lt_top
  have hi := hmem.integrable_norm_pow' (p := 4)
  refine Integrable.mono' hi ((measurable_freshU b E X).norm.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (norm_nonneg _)]
  have := pow_le_pow_left₀ (norm_nonneg _) (norm_freshU_le b E X ω) 2
  rw [← pow_mul] at this; exact this

/-- The covariance products are integrable. -/
theorem freshU_hp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hT : T.PosSemidef) (U : Ω → Matrix (Fin W) (Fin W) ℂ) (hUm : Measurable U)
    (h2 : Integrable (fun ω => ‖U ω‖ ^ 2) μ) (i m : Fin W) :
    Integrable (fun ω => ts_ent hT (U ω - matrixExpect μ U) i m *
      ts_ent hT (U ω - matrixExpect μ U) m i) μ := by
  have hZ : Measurable fun ω => U ω - matrixExpect μ U := hUm.sub_const _
  refine Integrable.mono' ((h2.const_mul 2).add (integrable_const (2 * ‖matrixExpect μ U‖ ^ 2)))
    ((ts_measurable_ent hT hZ i m).mul (ts_measurable_ent hT hZ m i)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  show ‖_ * _‖ ≤ 2 * ‖U ω‖ ^ 2 + 2 * ‖matrixExpect μ U‖ ^ 2
  rw [norm_mul]
  have a1 := ts_norm_ent_le hT (U ω - matrixExpect μ U) i m
  have a2 := ts_norm_ent_le hT (U ω - matrixExpect μ U) m i
  have a3 := norm_sub_le (U ω) (matrixExpect μ U)
  have := mul_le_mul a1 a2 (norm_nonneg _) (norm_nonneg _)
  have := mul_le_mul a3 a3 (norm_nonneg _) (by positivity)
  nlinarith [norm_nonneg (U ω), norm_nonneg (matrixExpect μ U),
    sq_nonneg (‖U ω‖ - ‖matrixExpect μ U‖)]

/-- **HS moments of `B = sand T U⁰`**, bulk-uniform. -/
theorem hs_moments_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      ∀ hT : (passiveTransmission b E X).PosSemidef,
        Integrable (fun ω => frobSq (sand hT (freshU b E X ω -
          matrixExpect (freshLaw W b) (freshU b E X)))) (freshLaw W b) ∧
        ∫ ω, frobSq (sand hT (freshU b E X ω - matrixExpect (freshLaw W b) (freshU b E X)))
          ∂freshLaw W b ≤ (C / Real.sqrt W * (passiveTransmission b E X).trace.re) ^ 2 ∧
        Integrable (fun ω => ‖sand hT (freshU b E X ω -
          matrixExpect (freshLaw W b) (freshU b E X))‖ * frobSq (sand hT (freshU b E X ω -
          matrixExpect (freshLaw W b) (freshU b E X)))) (freshLaw W b) ∧
        ∫ ω, ‖sand hT (freshU b E X ω - matrixExpect (freshLaw W b) (freshU b E X))‖ *
          frobSq (sand hT (freshU b E X ω - matrixExpect (freshLaw W b) (freshU b E X)))
          ∂freshLaw W b ≤ (C / Real.sqrt W * (passiveTransmission b E X).trace.re) ^ 3 := by
  obtain ⟨C2, W2, hC2⟩ := oneStepFluctuation_bulk hA hb0 hb hκ ((2 : ℕ) : ℝ) (by norm_num)
  obtain ⟨C3, W3, hC3⟩ := oneStepFluctuation_bulk hA hb0 hb hκ ((3 : ℕ) : ℝ) (by norm_num)
  obtain ⟨Wi, hUi⟩ := ml_integrable_U_bulk hA hb0 hb hκ
  set C := max (max C2 C3) 0
  refine ⟨C, max (max W2 W3) (max Wi 1), le_max_right _ _, fun W hW E hE X hX hT => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW2, hW3⟩, hWi, hW1⟩ := hW
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
  have hbil : ∀ (Cx : ℝ) (p : ℕ), Cx ≤ C → (∀ u v : Fin W → ℂ, eLpNorm (fun ω => bilinear u
      (Z ω) v) (ENNReal.ofReal (p : ℝ)) μ ≤ ENNReal.ofReal (Cx / Real.sqrt W * vecNorm u *
        vecNorm v)) → ∀ u v : Fin W → ℂ, eLpNorm (fun ω => bilinear u (Z ω) v)
        (ENNReal.ofReal (p : ℝ)) μ ≤ ENNReal.ofReal (C / Real.sqrt W * vecNorm u * vecNorm v) :=
    fun Cx p hCx h u v => (h u v).trans (ENNReal.ofReal_le_ofReal (by
      have := vecNorm_nonneg u; have := vecNorm_nonneg v
      have : Cx / Real.sqrt W ≤ C / Real.sqrt W :=
        div_le_div_of_nonneg_right hCx (Real.sqrt_nonneg _)
      gcongr))
  have hmom : ∀ p : ℕ, 2 ≤ p → (∀ u v : Fin W → ℂ, eLpNorm (fun ω => bilinear u (Z ω) v)
      (ENNReal.ofReal (p : ℝ)) μ ≤ ENNReal.ofReal (C / Real.sqrt W * vecNorm u * vecNorm v)) →
      ∫ ω, Real.sqrt (frobSq (B ω)) ^ p ∂μ ≤
        (C / Real.sqrt W * (passiveTransmission b E X).trace.re) ^ p := by
    intro p hp hb'
    have h := eLpNorm_hsSandwich_le μ hT hZm (p := ENNReal.ofReal (p : ℝ))
      (by rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num]
          exact ENNReal.ofReal_le_ofReal (by exact_mod_cast hp))
      (by positivity) hb'
    simp only [hhs] at h
    exact mp_integral_pow_le (Filter.Eventually.of_forall fun _ => Real.sqrt_nonneg _) p
      (by omega) hσ h
  have hm2 := hmom 2 le_rfl (hbil C2 2 ((le_max_left _ _).trans (le_max_left _ _))
    (hC2 W hW2 E hE X hX · · |>.1))
  have hm3 := hmom 3 (by norm_num) (hbil C3 3 ((le_max_right _ _).trans (le_max_left _ _))
    (hC3 W hW3 E hE X hX · · |>.1))
  have hFm : Measurable fun ω => frobSq (B ω) := continuous_frobSq.measurable.comp hBm
  have hI2 : Integrable (fun ω => frobSq (B ω)) μ :=
    Integrable.of_bound hFm.aestronglyMeasurable (4 * W) (by
      filter_upwards [hfr] with ω hω
      rwa [Real.norm_of_nonneg (frobSq_nonneg _)])
  have hsq : ∀ ω, Real.sqrt (frobSq (B ω)) ^ 2 = frobSq (B ω) := fun ω =>
    Real.sq_sqrt (frobSq_nonneg _)
  have hI3' : Integrable (fun ω => Real.sqrt (frobSq (B ω)) ^ 3) μ :=
    Integrable.of_bound ((Real.continuous_sqrt.measurable.comp hFm).pow_const 3).aestronglyMeasurable
      ((4 * W + 1) ^ 3) (by
        filter_upwards [hfr] with ω hω
        rw [Real.norm_of_nonneg (by positivity)]
        have : Real.sqrt (frobSq (B ω)) ≤ 4 * W + 1 :=
          Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith [Nat.cast_nonneg (α := ℝ) W]⟩
        exact pow_le_pow_left₀ (Real.sqrt_nonneg _) this 3)
  have hpt : ∀ ω, ‖B ω‖ * frobSq (B ω) ≤ Real.sqrt (frobSq (B ω)) ^ 3 := fun ω => by
    have := norm_le_sqrt_frobSq (B ω)
    rw [show Real.sqrt (frobSq (B ω)) ^ 3 = Real.sqrt (frobSq (B ω)) * frobSq (B ω) by
      rw [pow_succ', hsq]]
    exact mul_le_mul_of_nonneg_right this (frobSq_nonneg _)
  have hI3 : Integrable (fun ω => ‖B ω‖ * frobSq (B ω)) μ :=
    Integrable.mono' hI3' (hBm.norm.mul hFm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (frobSq_nonneg _))]; exact hpt ω)
  refine ⟨hI2, ?_, hI3, ?_⟩
  · calc ∫ ω, frobSq (B ω) ∂μ = ∫ ω, Real.sqrt (frobSq (B ω)) ^ 2 ∂μ :=
          integral_congr_ae (Filter.Eventually.of_forall fun ω => (hsq ω).symm)
      _ ≤ _ := hm2
  · exact (integral_mono hI3 hI3' hpt).trans hm3

end BlockBand.Transmission.Generator
