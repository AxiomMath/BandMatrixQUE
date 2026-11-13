module

public import BlockBand.SourceProcess.ProjSeparator.FarTrace
public import BlockBand.SourceProcess.ContractingWords.SlotMom

/-!
# The far injected trace `InjFarTrace`

`injFarTrace_holds`: under `GaussianAbsorptionContract`, the far injected trace of one fresh
layer is `O(g)`, `g` the conductance.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ProjSeparator

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.Bridge BlockBand.Transmission.PassiveCovariance
open BlockBand.Transmission.PassiveLayer BlockBand.SourceProcess.ContractingWords
open scoped ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- `E‖Δ‖² ≤ C²` from `‖‖Δ‖‖_{L²} ≤ C`. -/
theorem sq_moment_of_momBd {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} {C : ℝ} (hC : 0 ≤ C) (h : MomBd μ f 2 C) :
    Integrable (fun ω => f ω ^ 2) μ ∧ ∫ ω, f ω ^ 2 ∂μ ≤ C ^ 2 := by
  obtain ⟨hm, hb⟩ := h
  have hmc : AEStronglyMeasurable (fun ω => ((f ω : ℝ) : ℂ)) μ :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hm
  have he : eLpNorm (fun ω => ((f ω : ℝ) : ℂ)) ((2 : ℕ) : ℝ≥0∞) μ = eLpNorm f 2 μ :=
    eLpNorm_congr_norm_ae hmc hm (Filter.Eventually.of_forall fun ω => Complex.norm_real _)
  have hb' : eLpNorm (fun ω => ((f ω : ℝ) : ℂ)) ((2 : ℕ) : ℝ≥0∞) μ ≤ ENNReal.ofReal C := by
    rw [he]; simpa using hb
  obtain ⟨hi, hle⟩ := moments_of_eLpNorm hmc hC hb' 2 (by norm_num) le_rfl
  have e : (fun ω => ‖((f ω : ℝ) : ℂ)‖ ^ 2) = fun ω => f ω ^ 2 := by
    funext ω; rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [e] at hi hle
  exact ⟨hi, hle⟩

/-- **`InjFarTrace` from `GaussianAbsorptionContract`.** -/
theorem injFarTrace_holds (hGA : GaussianAbsorptionContract) : InjFarTrace := by
  intro b hb0 hb κ hκ
  obtain ⟨C, W₀, hC, h⟩ := FullSource.delta_moments hGA b hb0 hb κ hκ 2 (by norm_num)
  set ηL := (1 - b) * κ / 4
  have hηL : 0 < ηL := by
    have : 0 < 1 - b := by linarith
    positivity
  set a := ηL⁻¹
  refine ⟨a ^ 2 * (2 + 2 * a ^ 2 * C ^ 2), W₀, by positivity, fun W hW E hE XX hXX => ?_⟩
  have hE1 : -2 < E := by have := hE.1; linarith
  have hE2 : E < 2 := by have := hE.2; linarith
  have hη := etaZ_pos b E (by linarith) hE1 hE2
  have hηge : ηL ≤ etaZ b E := FullSource.etaZ_ge hb0 hb hκ hE
  have hia : (etaZ b E)⁻¹ ≤ a := inv_anti₀ hηL hηge
  set X := nearSchur (boundaryZ b E) XX
  set g := conductanceOf (passiveTransmission b E X)
  have hY : (passiveY X).PosSemidef := FullSource.nearSchur_passive hη hXX
  have hg0 : 0 ≤ g := FullSourceCovariance.conductance_nonneg b E hη.le hY
  set μ := freshLaw W b
  set S := g / (4 * etaZ b E ^ 2)
  have hS0 : 0 ≤ S := by positivity
  obtain ⟨hint2, hle2⟩ := sq_moment_of_momBd hC (h W hW E hE X hY)
  set Δn : LayerSample W .oneBlockOnePort → ℝ := fun ω => ‖freshDelta b E X ω‖
  have hG : Integrable (fun ω => (2 + 2 * a ^ 2 * Δn ω ^ 2) * S) μ :=
    ((integrable_const 2).add (hint2.const_mul (2 * a ^ 2))).mul_const S
  have hpt : ∀ ω, ‖((freshD b E XX ω)ᴴ * freshD b E XX ω * (1 - nearProjection W)).trace‖ ≤
      (2 + 2 * a ^ 2 * Δn ω ^ 2) * S := by
    intro ω
    refine (norm_trace_far_le hb0 hb hE1 hE2 hXX ω).trans
      (mul_le_mul_of_nonneg_right ?_ hS0)
    have ht : 0 ≤ Δn ω := norm_nonneg _
    have h1 : (etaZ b E)⁻¹ * Δn ω ≤ a * Δn ω := mul_le_mul_of_nonneg_right hia ht
    have h0 : 0 ≤ (etaZ b E)⁻¹ * Δn ω := mul_nonneg (inv_nonneg.mpr hη.le) ht
    nlinarith [sq_nonneg ((etaZ b E)⁻¹ * Δn ω - 1)]
  have hint : ∫ ω, (2 + 2 * a ^ 2 * Δn ω ^ 2) * S ∂μ = (2 + 2 * a ^ 2 * ∫ ω, Δn ω ^ 2 ∂μ) * S := by
    rw [integral_mul_const, integral_add (integrable_const _) (hint2.const_mul _),
      integral_const_mul, integral_const]
    simp [Δn, μ]
  have hSa : S ≤ a ^ 2 * g := by
    have : S = (etaZ b E)⁻¹ ^ 2 * g / 4 := by simp only [S]; field_simp
    rw [this]
    have := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (inv_nonneg.mpr hη.le) hia 2) hg0
    nlinarith [sq_nonneg (etaZ b E)⁻¹]
  calc ‖∫ ω, ((freshD b E XX ω)ᴴ * freshD b E XX ω * (1 - nearProjection W)).trace ∂μ‖
      ≤ ∫ ω, ‖((freshD b E XX ω)ᴴ * freshD b E XX ω * (1 - nearProjection W)).trace‖ ∂μ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ ω, (2 + 2 * a ^ 2 * Δn ω ^ 2) * S ∂μ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) hG
          (Filter.Eventually.of_forall hpt)
    _ = (2 + 2 * a ^ 2 * ∫ ω, Δn ω ^ 2 ∂μ) * S := hint
    _ ≤ (2 + 2 * a ^ 2 * C ^ 2) * (a ^ 2 * g) := by
        have : 0 ≤ 2 + 2 * a ^ 2 * C ^ 2 := by positivity
        have h2 : 2 + 2 * a ^ 2 * ∫ ω, Δn ω ^ 2 ∂μ ≤ 2 + 2 * a ^ 2 * C ^ 2 := by
          gcongr
        exact mul_le_mul h2 hSa hS0 this
    _ = a ^ 2 * (2 + 2 * a ^ 2 * C ^ 2) * g := by ring

end BlockBand.SourceProcess.ProjSeparator
