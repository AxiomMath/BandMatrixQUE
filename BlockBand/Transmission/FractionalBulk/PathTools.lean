module

public import BlockBand.Transmission.FractionalBulk.StepBound
public import BlockBand.Transmission.Generator.DriftCond

/-!
# Path-level tools

* `pow2_of_eLpNorm`: `‖f‖_2 ≤ C` gives `E f² ≤ C²`;
* `sq_integral_le`: `(E f)² ≤ E f²` on a probability space;
* `integral_fresh_eq`: `E Ψ(X_r, fresh_r) = E ∫ Ψ(X_r, y) dfresh(y)` for bounded measurable `Ψ`
  (`condExp_fresh` and the tower property);
* `ae_pathFrac_succ`: a.s. `Tr T_{r+1}^p = stepFrac p b E X_r fresh_r` (`r ≥ 1`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.FractionalBulk

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.Bridge
open BlockBand.Transmission.SourceMixing BlockBand.Transmission.Generator
open scoped ENNReal ComplexOrder

variable {W : ℕ}

theorem pow2_of_eLpNorm {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) {C : ℝ} (hC : 0 ≤ C)
    (h : eLpNorm f (ENNReal.ofReal 2) μ ≤ ENNReal.ofReal C) :
    Integrable (fun ω => f ω ^ 2) μ ∧ ∫ ω, f ω ^ 2 ∂μ ≤ C ^ 2 := by
  have hlt : eLpNorm f (ENNReal.ofReal 2) μ < ∞ := lt_of_le_of_lt h ENNReal.ofReal_lt_top
  have hmem : MemLp f ((2 : ℕ) : ℝ≥0∞) μ := by
    have : ENNReal.ofReal 2 = ((2 : ℕ) : ℝ≥0∞) := by norm_num
    rw [← this]; exact hlt
  have hint : Integrable (fun ω => f ω ^ 2) μ := by
    have := hmem.integrable_norm_pow' (p := 2)
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Real.norm_eq_abs, sq_abs]
  refine ⟨hint, ?_⟩
  have hl := SourceMixing.cm_lintegral_le hf (p := 2) (by norm_num) hC h
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω => sq_nonneg (f ω))
    hint.aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) (le_trans (le_of_eq ?_) (hl.trans
    (le_of_eq (by rw [show (C ^ (2 : ℝ)) = C ^ 2 by norm_cast]))))
  refine lintegral_congr fun ω => ?_
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two,
    Real.norm_eq_abs, sq_abs]

theorem sq_integral_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : Integrable f μ) (hf2 : Integrable (fun ω => f ω ^ 2) μ) :
    (∫ ω, f ω ∂μ) ^ 2 ≤ ∫ ω, f ω ^ 2 ∂μ := by
  set m := ∫ ω, f ω ∂μ
  have h0 : 0 ≤ ∫ ω, (f ω - m) ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
  have hexp : ∫ ω, (f ω - m) ^ 2 ∂μ = ∫ ω, f ω ^ 2 ∂μ - m ^ 2 := by
    have e : ∀ ω, (f ω - m) ^ 2 = f ω ^ 2 + (-(2 * m) * f ω + m ^ 2) := fun ω => by ring
    simp_rw [e]
    have hg : Integrable (fun ω => -(2 * m) * f ω + m ^ 2) μ :=
      (hf.const_mul _).add (integrable_const _)
    rw [integral_add hf2 hg, integral_add (hf.const_mul _) (integrable_const _), integral_const_mul,
      integral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    ring
  linarith

/-- **One fresh layer along the path**: `E Ψ(X_r, fresh_r) = E ∫ Ψ(X_r, y) dfresh`. -/
theorem integral_fresh_eq (b E : ℝ)
    {Ψ : Matrix (Fin W) (Fin W) ℂ × LayerSample W .oneBlockOnePort → ℝ} (hΨ : Measurable Ψ)
    {M : ℝ} (hΨM : ∀ x, |Ψ x| ≤ M) (j : ℕ) :
    ∫ ω, Ψ (pathX b E W j ω, freshSample W j ω) ∂growthPathLaw W b =
      ∫ ω, (∫ y, Ψ (pathX b E W j ω, y) ∂freshLaw W b) ∂growthPathLaw W b := by
  have h := condExp_fresh b E hΨ hΨM j
  rw [← integral_condExp (growthSigma_le W j)]
  exact integral_congr_ae h

/-- **A.s. `Tr T_{r+1}^p = stepFrac p b E X_r fresh_r`**, `r ≥ 1`. -/
theorem ae_pathFrac_succ {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {b : ℝ} (hb : b < 1 / 2)
    (hW : 1 ≤ W) {E : ℝ} (h1 : -2 < E) (h2 : E < 2) {r : ℕ} (hr : 1 ≤ r) :
    ∀ᵐ ω ∂growthPathLaw W b, fracTrace p (pathTransmission b E (fun _ => 0) W (r + 1) ω) =
      stepFrac p b E (pathX b E W r ω) (freshSample W r ω) := by
  filter_upwards [ae_pathX_succ hb h1 h2 hW, mm_ae_passive (W := W) (b := b) (by linarith) h1 h2
    (r + 1)] with ω hs hpas
  have hT : (passiveTransmission b E (pathX b E W (r + 1) ω)).PosSemidef :=
    passiveTransmission_posSemidef (by linarith) h1 h2 hpas
  have hT1 := one_sub_passiveTransmission_posSemidef b E (pathX b E W (r + 1) ω)
  have e : pathTransmission b E (fun _ => 0) W (r + 1) ω =
      passiveTransmission b E (pathX b E W (r + 1) ω) := rfl
  rw [e, stepFrac, ← hs r hr, ← fracTrace_eq_fracInt hT hp0 hp1]
  have h0 := fracTrace_nonneg' p (passiveTransmission b E (pathX b E W (r + 1) ω))
  have hle := fracTrace_le_card hT hT1 hp0
  rw [Fintype.card_fin] at hle
  rw [clipW_of_mem h0 hle]

end BlockBand.Transmission.FractionalBulk
