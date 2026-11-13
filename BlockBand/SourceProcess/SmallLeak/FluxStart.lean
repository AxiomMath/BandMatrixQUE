module

public import BlockBand.SourceProcess.SmallLeak.StartAlg
public import BlockBand.SourceProcess.SmallLeak.Interface
public import BlockBand.Transmission.FractionalBulk.Main
public import BlockBand.SourceProcess.TagBirth.Main

/-!
# The omitted flux at the closing time

This file proves `OmittedFluxStart`. Almost surely the path scattering matrix at `n_s = ⌊Ws⌋` is
the two-port scattering matrix of the Hermitian `𝕏_{n_s}` (`Bridge.scatteringMatrix_eq`), so
`g_{n_s} ≤ h Tr T_{n_s}^{1/2}` (`start_flux_le`); the fractional transmission bound
`fractionalBulk_holds` (`p = 1/2`, `t = s`) bounds the mean.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.SmallLeak

open MeasureTheory Filter Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.Bridge BlockBand.SourceProcess.Closing
open BlockBand.SourceProcess.FullSourceStops BlockBand.Transmission.FractionalBulk
open BlockBand.SourceProcess.TagBirth
open scoped ENNReal

variable {W : ℕ}

/-- Almost surely `g_{n} ≤ h Tr T_n^{1/2}` at the closing length `n = ⌊Ws⌋`. -/
theorem ae_start_flux_le {b E : ℝ} (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) (hW : 1 ≤ W)
    {h : ℝ} (hh : 0 ≤ h) (s : ℝ) :
    ∀ᵐ ω ∂growthPathLaw W b, omittedFlux b E h s W ⌊(W : ℝ) * s⌋₊ ω ≤
      h * fracTrace (1 / 2) (pathTransmission b E (fun _ => 0) W ⌊(W : ℝ) * s⌋₊ ω) := by
  have hη : 0 < etaZ b E := boundaryZ_im_pos (by linarith) hE1 hE2
  filter_upwards [ae_isUnit_pathPencil_growth hb hW E, ae_growth_isHermitian W b] with ω hF hA
  set n := ⌊(W : ℝ) * s⌋₊
  have hXX := pathSchur_isHermitian E n ω hA
  have hS := scatteringMatrix_eq b E n ω (hF n)
  have := start_flux_le hη hXX hh
  simp only at this
  rw [pathTransmission, ← pathX, pathX_eq]
  unfold omittedFlux farOmitted nearOut omittedProj farTransmission farReflection
  rw [hS]
  exact this

/-- **`OmittedFluxStart`** from the input hypotheses of. -/
theorem omittedFluxStart_holds (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : GaussianPoincare) : OmittedFluxStart := by
  intro b hb0 hb E hE1 hE2 s hs
  obtain ⟨hκ, hEκ⟩ := mem_bulkInterval_self hE1 hE2
  obtain ⟨C, hC⟩ := fractionalBulk_holds hMT hGA hLp hP b hb0 hb _ hκ (1 / 2) (by norm_num)
    (by norm_num) s hs
  refine ⟨max C 0, fun h h0 _ => ?_⟩
  obtain ⟨W₀, hW₀⟩ := hC s le_rfl
  filter_upwards [eventually_ge_atTop (max W₀ 1)] with W hW
  have hW1 : 1 ≤ W := le_trans (le_max_right _ _) hW
  have hWW : W₀ ≤ W := le_trans (le_max_left _ _) hW
  set n := ⌊(W : ℝ) * s⌋₊
  have hae := ae_start_flux_le (W := W) hb hE1 hE2 hW1 h0.le s
  have hmeas := measurable_omittedFlux (W := W) b E h s n
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (omittedFlux_nonneg b E h s W n))
    hmeas.aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  calc ∫⁻ ω, ENNReal.ofReal (omittedFlux b E h s W n ω) ∂growthPathLaw W b
      ≤ ∫⁻ ω, ENNReal.ofReal h * ENNReal.ofReal
          (fracTrace (1 / 2) (pathTransmission b E (fun _ => 0) W n ω)) ∂growthPathLaw W b :=
        lintegral_mono_ae (hae.mono fun ω hω => by
          rw [← ENNReal.ofReal_mul h0.le]; exact ENNReal.ofReal_le_ofReal hω)
    _ = ENNReal.ofReal h * ∫⁻ ω, ENNReal.ofReal
          (fracTrace (1 / 2) (pathTransmission b E (fun _ => 0) W n ω)) ∂growthPathLaw W b :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal h * ENNReal.ofReal (max C 0) :=
        mul_le_mul_right ((hW₀ W hWW E hEκ).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))) _
    _ = ENNReal.ofReal (max C 0 * h) := by
        rw [← ENNReal.ofReal_mul h0.le, mul_comm]

end BlockBand.SourceProcess.SmallLeak
