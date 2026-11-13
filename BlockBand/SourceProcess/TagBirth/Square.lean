module

public import BlockBand.SourceProcess.FullSource.SqClock
public import BlockBand.SourceProcess.TagBirth.Interface

/-!
# The vanishing squared trace of a tag at its birth

* `enorm_trace_sq_eq`: `|Tr(Y/W)²| = W⁻¹ h`, `h = W⁻¹ Re Tr Y²` (`tagSq`);
* `tagBirthSquare_of hS`: the field `square` of `TagBirthValueEnergyUniformContract`, from
  FullSource's `SqBirthMoments` at `q = 1` (`E h_{k+1;k} ≤ B` uniformly in `k` and `E`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.TagBirth

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.FullSource
open scoped ENNReal

variable {W : ℕ}

theorem enorm_trace_sq_eq (b E : ℝ) (j k : ℕ) (ω : GrowthPath W) :
    ‖(((W : ℂ)⁻¹ • tagResponse b E W j k ω) ^ 2).trace‖ₑ =
      ENNReal.ofReal ((W : ℝ)⁻¹ * tagSq b E W j k ω) := by
  set Y := tagResponse b E W j k ω
  have hY : Y.IsHermitian := by
    rw [show Y = _ from tagResponse_eq_factor b E j k ω]
    exact Matrix.isHermitian_conjTranspose_mul_self _
  have hre := trace_factor_eq_re Y
  have hnn := trace_factor_re_nonneg Y
  rw [hY.eq] at hre hnn
  have e : (((W : ℂ)⁻¹ • Y) ^ 2).trace = (((W : ℝ)⁻¹ * ((W : ℝ)⁻¹ * (Y * Y).trace.re) : ℝ) : ℂ) := by
    rw [sq, smul_mul_smul_comm, Matrix.trace_smul, smul_eq_mul]
    conv_lhs => rw [hre]
    push_cast; ring
  rw [e, ← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rfl

/-- **The field `square`** of `TagBirthValueEnergyUniformContract`. -/
theorem tagBirthSquare_of (hS : SqBirthMoments) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI → ∀ ε T : ℝ, 0 < ε → ε < T →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI,
      ∀ k : ℕ, ε * W ≤ k → ((k + 1 : ℕ) : ℝ) ≤ T * W →
        ∫⁻ ω, ‖(((W : ℂ)⁻¹ • tagResponse b E W (k + 1) k ω) ^ 2).trace‖ₑ ∂growthPathLaw W b ≤
          ENNReal.ofReal (C / W) := by
  intro b hb0 hb κ hκ ε T _ _
  obtain ⟨B, W₀, hB0, hB⟩ := hS b hb0 hb κ hκ 1 le_rfl
  refine ⟨B, W₀, fun W hW E hE k _ _ => ?_⟩
  have hm := (measurable_tagSq (W := W) b E (k + 1) k).ennreal_ofReal
  simp only [enorm_trace_sq_eq]
  calc ∫⁻ ω, ENNReal.ofReal ((W : ℝ)⁻¹ * tagSq b E W (k + 1) k ω) ∂growthPathLaw W b
      = ENNReal.ofReal (W : ℝ)⁻¹ *
          ∫⁻ ω, ENNReal.ofReal (tagSq b E W (k + 1) k ω) ∂growthPathLaw W b := by
        rw [← lintegral_const_mul _ hm]
        exact lintegral_congr fun ω => ENNReal.ofReal_mul (by positivity)
    _ ≤ ENNReal.ofReal (W : ℝ)⁻¹ * ENNReal.ofReal B := by
        gcongr
        simpa using hB W hW E hE k
    _ = ENNReal.ofReal (B / W) := by
        rw [← ENNReal.ofReal_mul (by positivity), div_eq_inv_mul]

end BlockBand.SourceProcess.TagBirth
