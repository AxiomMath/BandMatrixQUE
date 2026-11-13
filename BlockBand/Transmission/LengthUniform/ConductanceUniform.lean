module

public import BlockBand.Transmission.LengthUniform.BulkMassMoment
public import BlockBand.Transmission.LengthUniform.Jet

/-!
# The length-uniform conductance moments

Law `growthPathLaw W b`; hypotheses `MatchedTracesContract`, `GaussianAbsorptionContract` and
`GaussianLpGradient`.

`lengthUniform_conductance_holds`: the `L^p` moments of the conductance `g_r` on `εW ≤ r ≤ TW` are
bounded by a constant chosen before the total length `T`, uniformly on the bulk.
`transmissionLengthUniform_holds`: `TransmissionLengthUniformContract` holds (with
`lengthUniform_jet_holds` for the jet field).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LengthUniform

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Transmission BlockBand.Transmission.PathScalar BlockBand.Transmission.SourceMixing
open scoped ENNReal

/-- **`TransmissionLengthUniformContract.conductance`** from the input hypotheses. -/
theorem lengthUniform_conductance_holds (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI ε p : ℝ, 0 < κI → 0 < ε → 1 ≤ p →
      ∃ C : ℝ, ∀ T : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI, ∀ r : ℕ,
        ε * W ≤ r → (r : ℝ) ≤ T * W →
          ∫⁻ ω, ‖pathConductance b E W r ω‖ₑ ^ p ∂growthPathLaw W b ≤ ENNReal.ofReal C := by
  intro b hb0 hb κI ε p hκ hε hp
  obtain ⟨K, hK, hKT⟩ := massMomentBound_bulk hMT hGA hLp hb0 hb hκ p hp
  have hp0 : 0 < p := by linarith
  refine ⟨(4 * K * (1 + ε⁻¹)) ^ p, fun T => ?_⟩
  obtain ⟨W₀, hW₀⟩ := hKT T
  refine ⟨max W₀ 1, fun W hW E hE r hεr hrT => ?_⟩
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  have hWW : W₀ ≤ W := le_of_max_le_left hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast le_of_max_le_right hW
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le (by nlinarith) hεr
  have hr1 : 1 ≤ r := by
    have : 0 < r := by exact_mod_cast hr0
    omega
  have hη := PassiveCovariance.etaZ_pos b E (by linarith) h1 h2
  have hη1 : etaZ b E ≤ 1 := bulk_eta_le_one hb0 hκ hE
  set P := growthPathLaw W b
  have hq := hW₀ W hWW E hE r hr1 hrT
  have hgL : eLpNorm (pathConductance b E W r) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (4 * etaZ b E * (K * (1 + W / r))) := by
    have e : pathConductance b E W r =
        (4 * etaZ b E) • fun ω => passiveMass b E (pathX b E W r ω) := by
      funext ω; rw [pathConductance_eq_mass]; rfl
    rw [e, eLpNorm_const_smul, ENNReal.ofReal_mul (by positivity), Real.enorm_eq_ofReal_abs,
      abs_of_pos (by positivity)]
    exact mul_le_mul_right hq _
  have hWr : (W : ℝ) / r ≤ ε⁻¹ := by
    rw [div_le_iff₀ hr0, inv_mul_eq_div, le_div_iff₀ hε]; linarith
  have hle : 4 * etaZ b E * (K * (1 + W / r)) ≤ 4 * K * (1 + ε⁻¹) := by
    have h3 : K * (1 + W / r) ≤ K * (1 + ε⁻¹) := mul_le_mul_of_nonneg_left (by linarith) hK
    have h4 : 0 ≤ K * (1 + W / r) := by positivity
    nlinarith
  have hg := (measurable_pathConductance (W := W) b E r).aestronglyMeasurable (μ := P)
  refine (cm_lintegral_le hg hp0 (by positivity) hgL).trans (ENNReal.ofReal_le_ofReal ?_)
  exact Real.rpow_le_rpow (by positivity) hle hp0.le

/-- **The `TransmissionLengthUniformContract`** from the input hypotheses
`MatchedTracesContract`, `GaussianAbsorptionContract` and `GaussianLpGradient`.
-/
theorem transmissionLengthUniform_holds (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) :
    TransmissionLengthUniformContract where
  conductance := lengthUniform_conductance_holds hMT hGA hLp
  jet := lengthUniform_jet_holds hMT hGA hLp

end BlockBand.Transmission.LengthUniform
