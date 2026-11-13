module

public import BlockBand.Transmission.Generator.BrFour
public import BlockBand.Transmission.Generator.BrLayer

/-!
# One-layer fourth moment of the increment, bulk-uniform (input of `PowerModulusAlong`)

* `hs_moment8_bulk`: `E‖sand T Z‖⁸_HS ≤ (C Tr T/√W)⁸` (`oneStepFluctuation_bulk`, `p = 8`);
* `brLin_moment4_bulk`: `E|λ_{k+1}(Z)|⁴ ≤ (C Tr T/√W)⁴` (`p = 4`, `eLpNorm_brLin_le`).

These are the inputs of **`fourth_layer_bulk hGA hLp`**, proved in the sibling module (with the
bookkeeping lemma `br4_rhs_le`): `b, κ, k` first; then `K ≥ 0, W₀`; for `W ≥ W₀`,
`E ∈ bulkInterval κ`, every `s : ℂ` and passive `X`:
`E(Re Tr T(X₊)^{k+1} - Re Tr T^{k+1})⁴ ≤ K·brY¹²/W²`. No `GaussianPoincare`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveCovariance
open BlockBand.Transmission.PassiveLayer BlockBand.Transmission.SourceMixing
open BlockBand.Transmission.LengthUniform BlockBand.Transmission.PathScalar
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator ENNReal

variable {W : ℕ}

/-- Bulk-uniform bilinear `L^p` bounds of `Z = U - EU`, with `C ≥ 0`. -/
theorem bil_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) (p : ℕ) (hp : 1 ≤ p) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef → ∀ u v : Fin W → ℂ,
        eLpNorm (fun ω => bilinear u (freshU b E X ω -
            matrixExpect (freshLaw W b) (freshU b E X)) v) (ENNReal.ofReal (p : ℝ)) (freshLaw W b) ≤
          ENNReal.ofReal (C / Real.sqrt W * vecNorm u * vecNorm v) := by
  obtain ⟨C, W₀, hC⟩ := oneStepFluctuation_bulk hA hb0 hb hκ (p : ℝ) (by exact_mod_cast hp)
  refine ⟨max C 0, W₀, le_max_right _ _, fun W hW E hE X hX u v => ?_⟩
  refine ((hC W hW E hE X hX u v).1).trans (ENNReal.ofReal_le_ofReal ?_)
  have := vecNorm_nonneg u; have := vecNorm_nonneg v
  have : C / Real.sqrt W ≤ max C 0 / Real.sqrt W :=
    div_le_div_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
  gcongr

/-- **Eighth HS moment.** -/
theorem hs_moment8_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      ∀ hT : (passiveTransmission b E X).PosSemidef,
        Integrable (fun ω => frobSq (sand hT (freshU b E X ω -
          matrixExpect (freshLaw W b) (freshU b E X))) ^ 4) (freshLaw W b) ∧
        ∫ ω, frobSq (sand hT (freshU b E X ω - matrixExpect (freshLaw W b) (freshU b E X))) ^ 4
          ∂freshLaw W b ≤ (C / Real.sqrt W * (passiveTransmission b E X).trace.re) ^ 8 := by
  obtain ⟨C, W8, hC0, hC⟩ := bil_bulk hA hb0 hb hκ 8 (by norm_num)
  obtain ⟨Wi, hUi⟩ := ml_integrable_U_bulk hA hb0 hb hκ
  refine ⟨C, max (max W8 Wi) 1, hC0, fun W hW E hE X hX hT => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW8, hWi⟩, hW1⟩ := hW
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
  have hfr : ∀ᵐ ω ∂μ, frobSq (B ω) ≤ 4 * W := by
    filter_upwards [hS] with ω hω
    have hB2 : ‖B ω‖ ≤ 2 := by
      have : B ω = sand hT (U ω) - sand hT (matrixExpect μ U) := sand_sub hT _ _
      rw [this]; exact (norm_sub_le _ _).trans (by linarith)
    refine (frobSq_le_card _).trans ?_
    have := pow_le_pow_left₀ (norm_nonneg _) hB2 2
    nlinarith [Nat.cast_nonneg (α := ℝ) W]
  have hhs : ∀ ω, hsSandwich (passiveTransmission b E X) (Z ω) = Real.sqrt (frobSq (B ω)) :=
    fun ω => by
      rw [frobSq_sand, Real.sqrt_sq (show 0 ≤ hsSandwich (passiveTransmission b E X) (Z ω) from
        Real.sqrt_nonneg _)]
  have h := eLpNorm_hsSandwich_le μ hT hZm (p := ENNReal.ofReal ((8 : ℕ) : ℝ))
    (by rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num]
        exact ENNReal.ofReal_le_ofReal (by norm_num))
    (by positivity) (hC W hW8 E hE X hX)
  simp only [hhs] at h
  have hm8 := mp_integral_pow_le (Filter.Eventually.of_forall fun _ => Real.sqrt_nonneg _) 8
    (by norm_num) hσ h
  have hFm : Measurable fun ω => frobSq (B ω) := continuous_frobSq.measurable.comp hBm
  have hq : ∀ ω, Real.sqrt (frobSq (B ω)) ^ 8 = frobSq (B ω) ^ 4 := fun ω => by
    rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, Real.sq_sqrt (frobSq_nonneg _)]
  refine ⟨?_, ?_⟩
  · refine Integrable.of_bound (hFm.pow_const 4).aestronglyMeasurable ((4 * W) ^ 4) ?_
    filter_upwards [hfr] with ω hω
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (frobSq_nonneg _) hω 4
  · calc ∫ ω, frobSq (B ω) ^ 4 ∂μ = ∫ ω, Real.sqrt (frobSq (B ω)) ^ 8 ∂μ :=
          integral_congr_ae (Filter.Eventually.of_forall fun ω => (hq ω).symm)
      _ ≤ _ := hm8

/-- **Fourth moment of `λ_{k+1}(Z)`.** -/
theorem brLin_moment4_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      ∀ hT : (passiveTransmission b E X).PosSemidef, ∀ k : ℕ,
        Integrable (fun ω => ‖brLin hT (k + 1) (freshU b E X ω -
          matrixExpect (freshLaw W b) (freshU b E X))‖ ^ 4) (freshLaw W b) ∧
        ∫ ω, ‖brLin hT (k + 1) (freshU b E X ω -
          matrixExpect (freshLaw W b) (freshU b E X))‖ ^ 4 ∂freshLaw W b ≤
          (C / Real.sqrt W * (passiveTransmission b E X).trace.re) ^ 4 := by
  obtain ⟨C, W4, hC0, hC⟩ := bil_bulk hA hb0 hb hκ 4 (by norm_num)
  refine ⟨C, max W4 1, hC0, fun W hW E hE X hX hT k => ?_⟩
  simp only [max_le_iff] at hW
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  have hT1 : ∀ i, ts_lam hT i ≤ 1 :=
    ts_lam_le_one hT (one_sub_passiveTransmission_posSemidef b E X)
  have hTr : 0 ≤ (passiveTransmission b E X).trace.re := (mm_trace_posSemidef hT).1
  set Z := fun ω => freshU b E X ω - matrixExpect (freshLaw W b) (freshU b E X)
  have hZm : Measurable Z := (measurable_freshU b E X).sub_const _
  have hm : AEStronglyMeasurable (fun ω => brLin hT (k + 1) (Z ω)) (freshLaw W b) :=
    ((continuous_brLin hT (k + 1)).measurable.comp hZm).aestronglyMeasurable
  have h := eLpNorm_brLin_le hT hT1 (k := k + 1) (by omega) Z
    (p := ENNReal.ofReal ((4 : ℕ) : ℝ)) (by
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by norm_num]
      exact ENNReal.ofReal_le_ofReal (by norm_num))
    (div_nonneg hC0 (Real.sqrt_nonneg _)) (fun u v => by
      have := hC W hW.1 E hE X hX u v
      simpa only [mul_assoc] using this)
  rw [← eLpNorm_norm (fun ω => brLin hT (k + 1) (Z ω)) hm] at h
  have hmem : MemLp (fun ω => ‖brLin hT (k + 1) (Z ω)‖) ((4 : ℕ) : ℝ≥0∞) (freshLaw W b) := by
    have : ENNReal.ofReal ((4 : ℕ) : ℝ) = ((4 : ℕ) : ℝ≥0∞) := by norm_num
    rw [MemLp, ← this]; exact h.trans_lt ENNReal.ofReal_lt_top
  refine ⟨?_, ?_⟩
  · have := hmem.integrable_norm_pow' (p := 4)
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [norm_norm, Z]
  · have := mp_integral_pow_le (Filter.Eventually.of_forall fun ω => norm_nonneg _) 4 (by norm_num)
      (by positivity) h
    refine this.trans (le_of_eq ?_)
    ring

end BlockBand.Transmission.Generator
